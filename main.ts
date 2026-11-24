// Tiny stack VM for make.fun tiny-stack-vm-01 (ISA.md + reference vm.mjs).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [opcode, immediate bytes, pops, pushes] for every opcode of the ISA.
const OPS = [
  [0x00,0,0,0],[0x01,1,0,1],[0x02,4,0,1],[0x03,0,1,0],
  [0x04,0,1,2],[0x05,0,2,2],[0x06,0,2,3],[0x07,0,3,3],
  [0x10,0,2,1],[0x11,0,2,1],[0x12,0,2,1],[0x13,0,2,1],
  [0x14,0,2,1],[0x15,0,2,1],[0x16,0,2,1],[0x17,0,1,1],
  [0x18,0,2,1],[0x19,0,2,1],[0x1a,0,2,1],[0x1b,0,1,1],
  [0x1c,0,2,1],[0x1d,0,2,1],[0x1e,0,2,1],[0x20,0,2,1],
  [0x21,0,2,1],[0x22,0,2,1],[0x30,2,0,0],[0x31,2,1,0],
  [0x32,2,1,0],[0x33,2,0,0],[0x34,0,0,0],[0x40,0,1,1],
  [0x41,0,2,0],[0x50,0,1,0],[0x51,0,1,0],[0x52,0,0,1],
  [0x53,0,1,0],
];
const IMM = new Int8Array(256).fill(-1);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
for (const [o, i, p, u] of OPS) { IMM[o] = i; POP[o] = p; PSH[o] = u; }

const MIN_INT = -2147483648;

// Runs one program on its input bytes; returns { out, exit } where out is
// exactly the bytes written and exit is 0-255 (a trap's code included).
function run(prog, input) {
  const n = prog.length;
  const D = new Int32Array(256); // data stack
  let sp = 0;
  const C = new Int32Array(64); // call stack
  let cp = 0;
  const M = new Int32Array(256); // memory, all zero
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  const fin = (e) => ({ out: out.slice(0, ol), exit: e });
  for (;;) {
    if (steps === 1000000) return fin(10); // step limit
    if (pc < 0 || pc >= n) return fin(9); // pc outside the program
    const op = prog[pc];
    const im = IMM[op];
    if (im < 0) return fin(5); // unknown opcode
    if (pc + im >= n) return fin(9); // immediate cut off by the end
    steps++;
    const nx = pc + 1 + im;
    if (sp < POP[op]) return fin(2); // stack underflow
    if (sp - POP[op] + PSH[op] > 256) return fin(3); // stack overflow
    pc = nx;
    switch (op) {
      case 0x00: return fin(0); // HALT
      case 0x01: D[sp++] = (prog[nx - 1] << 24) >> 24; break; // PUSH8 sign-extended
      case 0x02: // PUSH32 little-endian, signed
        D[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG, wraps at MIN_INT
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break; // ADD wraps
          case 0x11: r = (a - b) | 0; break; // SUB wraps
          case 0x12: r = Math.imul(a, b); break; // MUL low 32 bits
          case 0x13: // DIV truncated toward zero; MIN_INT / -1 is MIN_INT
            if (b === 0) return fin(4);
            r = a === MIN_INT && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD, sign of a; x % -1 is 0
            if (b === 0) return fin(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU, unsigned
            if (b === 0) return fin(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU, unsigned
            if (b === 0) return fin(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // SHL, low 5 bits only
          case 0x1d: r = a >> (b & 31); break; // SHR arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU logical
          case 0x20: r = a === b ? 1 : 0; break; // EQ
          case 0x21: r = a < b ? 1 : 0; break; // LT signed
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU unsigned
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit target
        if (cp === 64) return fin(7);
        C[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return fin(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return fin(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE (v addr --)
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return fin(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: { // PRINT decimal ASCII, no newline
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return fin(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC, low byte
        if (ol + 1 > 65536) return fin(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < input.length ? input[ip++] : -1; break; // IN, -1 when used up
      case 0x53: return fin(D[--sp] & 255); // EXIT, low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const prog = readFileSync(join(I, id, 'program.bin'));
  let input;
  try { input = readFileSync(join(I, id, 'input.bin')); } catch { input = Buffer.alloc(0); }
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), String(r.exit) + '\n');
}
