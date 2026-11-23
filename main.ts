// A tiny stack VM for make.fun's tiny-stack-vm-01: a faithful interpreter of the ISA in the kit's
// generator/subject/ISA.md, matching the reference VM generator/subject/vm.mjs rule for rule.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = 'stdout.bin', X = 'exit.txt';

// opcode byte -> [immediate bytes, pops, pushes]; HALT is byte 0 and an absent entry is an unknown opcode
const SHAPE: number[][] = [[0, 0, 0]];
for (const [byte, imm, pops, pushes] of [
  [0x01, 1, 0, 1], [0x02, 4, 0, 1],
  [0x03, 0, 1, 0], [0x04, 0, 1, 2], [0x05, 0, 2, 2],
  [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1],
  [0x13, 0, 2, 1], [0x14, 0, 2, 1], [0x15, 0, 2, 1],
  [0x16, 0, 2, 1], [0x17, 0, 1, 1], [0x18, 0, 2, 1],
  [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1],
  [0x20, 0, 2, 1], [0x21, 0, 2, 1], [0x22, 0, 2, 1],
  [0x30, 2, 0, 0], [0x31, 2, 1, 0], [0x32, 2, 1, 0],
  [0x33, 2, 0, 0], [0x34, 0, 0, 0],
  [0x40, 0, 1, 1], [0x41, 0, 2, 0],
  [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
]) SHAPE[byte] = [imm, pops, pushes];

/** Runs `p` (bytes) on `inp` (bytes): the bytes it wrote and the exit code it ended with. */
function run(p: Uint8Array, inp: Uint8Array): { out: Buffer; code: number } {
  const n = p.length;
  const S: number[] = []; // data stack, at most 256 values
  const C: number[] = []; // call stack, at most 64 return addresses
  const M = new Int32Array(256); // 256 words of memory, all 0
  const out = Buffer.allocUnsafe(65536);
  let olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: out.subarray(0, olen), code });
  for (;;) {
    if (steps === 1_000_000) return end(10); // step limit
    if (pc < 0 || pc >= n) return end(9); // pc outside the program
    const op = p[pc];
    const shape = SHAPE[op];
    if (shape === undefined) return end(5); // unknown opcode
    const imm = shape[0];
    if (pc + imm >= n) return end(9); // immediate cut off
    steps++;
    const next = pc + 1 + imm;
    if (S.length < shape[1]) return end(2); // stack underflow
    if (S.length - shape[1] + shape[2] > 256) return end(3); // stack overflow
    pc = next;
    switch (op) {
      case 0x00: return end(0); // HALT
      case 0x01: S.push(p[next - 1] << 24 >> 24); break; // PUSH8
      case 0x02:
        S.push(p[next - 4] | p[next - 3] << 8 | p[next - 2] << 16 | p[next - 1] << 24); break; // PUSH32
      case 0x03: S.pop(); break; // POP
      case 0x04: S.push(S[S.length - 1]); break; // DUP
      case 0x05: { const t = S[S.length - 1]; S[S.length - 1] = S[S.length - 2]; S[S.length - 2] = t; break; } // SWAP
      case 0x06: S.push(S[S.length - 2]); break; // OVER
      case 0x07: S.push(S.splice(S.length - 3, 1)[0]); break; // ROT
      case 0x17: S[S.length - 1] = -S[S.length - 1] | 0; break; // NEG
      case 0x1b: S[S.length - 1] = ~S[S.length - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = S.pop()!, a = S.pop()!;
        let r: number;
        switch (op) {
          case 0x10: r = a + b | 0; break; // ADD
          case 0x11: r = a - b | 0; break; // SUB
          case 0x12: r = Math.imul(a, b); break; // MUL
          case 0x13: r = b === 0 ? 0 : a === -2147483648 && b === -1 ? a : Math.trunc(a / b) | 0; break; // DIV
          case 0x14: r = b === 0 ? 0 : b === -1 ? 0 : a % b | 0; break; // MOD
          case 0x15: r = b === 0 ? 0 : Math.floor((a >>> 0) / (b >>> 0)) | 0; break; // DIVU
          case 0x16: r = b === 0 ? 0 : (a >>> 0) % (b >>> 0) | 0; break; // MODU
          case 0x18: r = a & b; break; // AND
          case 0x19: r = a | b; break; // OR
          case 0x1a: r = a ^ b; break; // XOR
          case 0x1c: r = a << (b & 31); break; // SHL
          case 0x1d: r = a >> (b & 31); break; // SHR
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU
          case 0x20: r = a === b ? 1 : 0; break; // EQ
          case 0x21: r = a < b ? 1 : 0; break; // LT
          default: r = a >>> 0 < b >>> 0 ? 1 : 0; // LTU
        }
        if (b === 0 && op >= 0x13 && op <= 0x16) return end(4); // division by zero
        S.push(r);
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ
        const rel = (p[next - 2] | p[next - 1] << 8) << 16 >> 16;
        if (op === 0x30 || (op === 0x31 ? S.pop()! === 0 : S.pop()! !== 0)) pc = next + rel;
        break;
      }
      case 0x33: // CALL
        if (C.length === 64) return end(7); // call stack full
        C.push(next);
        pc = p[next - 2] | p[next - 1] << 8;
        break;
      case 0x34: // RET
        if (C.length === 0) return end(8); // call stack empty
        pc = C.pop()!;
        break;
      case 0x40: { // LOAD
        const a = S[S.length - 1];
        if (a < 0 || a > 255) return end(6);
        S[S.length - 1] = M[a];
        break;
      }
      case 0x41: { // STORE
        const a = S[S.length - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = S[S.length - 2];
        S.length -= 2;
        break;
      }
      case 0x50: { // PRINT
        const s = String(S.pop());
        if (olen + s.length > 65536) return end(11); // output limit
        out.write(s, olen, 'ascii');
        olen += s.length;
        break;
      }
      case 0x51: // PUTC
        if (olen === 65536) return end(11); // output limit
        out[olen++] = S.pop()! & 255;
        break;
      case 0x52: S.push(ip < inp.length ? inp[ip++] : -1); break; // IN
      case 0x53: return end(S.pop()! & 255); // EXIT
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const dir = join(O, id);
  mkdirSync(dir, { recursive: true });
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  writeFileSync(join(dir, D), r.out);
  writeFileSync(join(dir, X), `${r.code}\n`);
}
