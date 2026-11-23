// A tiny stack VM for make.fun's tiny-stack-vm-01: a faithful interpreter of the ISA in the kit's
// generator/subject/ISA.md, matching the reference VM generator/subject/vm.mjs rule for rule.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = 'stdout.bin', X = 'exit.txt';

// opcode byte -> [name, immediate bytes, pops, pushes]
const OPS: Record<number, [string, number, number, number]> = {
  0x00: ['HALT', 0, 0, 0], 0x01: ['PUSH8', 1, 0, 1], 0x02: ['PUSH32', 4, 0, 1],
  0x03: ['POP', 0, 1, 0], 0x04: ['DUP', 0, 1, 2], 0x05: ['SWAP', 0, 2, 2],
  0x06: ['OVER', 0, 2, 3], 0x07: ['ROT', 0, 3, 3],
  0x10: ['ADD', 0, 2, 1], 0x11: ['SUB', 0, 2, 1], 0x12: ['MUL', 0, 2, 1],
  0x13: ['DIV', 0, 2, 1], 0x14: ['MOD', 0, 2, 1], 0x15: ['DIVU', 0, 2, 1],
  0x16: ['MODU', 0, 2, 1], 0x17: ['NEG', 0, 1, 1], 0x18: ['AND', 0, 2, 1],
  0x19: ['OR', 0, 2, 1], 0x1a: ['XOR', 0, 2, 1], 0x1b: ['NOT', 0, 1, 1],
  0x1c: ['SHL', 0, 2, 1], 0x1d: ['SHR', 0, 2, 1], 0x1e: ['SHRU', 0, 2, 1],
  0x20: ['EQ', 0, 2, 1], 0x21: ['LT', 0, 2, 1], 0x22: ['LTU', 0, 2, 1],
  0x30: ['JMP', 2, 0, 0], 0x31: ['JZ', 2, 1, 0], 0x32: ['JNZ', 2, 1, 0],
  0x33: ['CALL', 2, 0, 0], 0x34: ['RET', 0, 0, 0],
  0x40: ['LOAD', 0, 1, 1], 0x41: ['STORE', 0, 2, 0],
  0x50: ['PRINT', 0, 1, 0], 0x51: ['PUTC', 0, 1, 0], 0x52: ['IN', 0, 0, 1],
  0x53: ['EXIT', 0, 1, 0],
};

/** Runs `p` (bytes) on `inp` (bytes): the bytes it wrote and the exit code it ended with. */
function run(p: Uint8Array, inp: Uint8Array): { out: Buffer; code: number } {
  const n = p.length;
  const S: number[] = []; // data stack, at most 256 values
  const C: number[] = []; // call stack, at most 64 return addresses
  const M = new Int32Array(256); // 256 words of memory, all 0
  const out: number[] = [];
  let ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: Buffer.from(out), code });
  for (;;) {
    if (steps === 1_000_000) return end(10); // step limit
    if (pc < 0 || pc >= n) return end(9); // pc outside the program
    const op = OPS[p[pc]];
    if (!op) return end(5); // unknown opcode
    const [name, imm, pops, pushes] = op;
    if (pc + imm >= n) return end(9); // immediate cut off
    steps++;
    const next = pc + 1 + imm;
    if (S.length < pops) return end(2); // stack underflow
    if (S.length - pops + pushes > 256) return end(3); // stack overflow
    pc = next;
    switch (name) {
      case 'HALT': return end(0);
      case 'PUSH8': S.push(p[next - 1] << 24 >> 24); break;
      case 'PUSH32':
        S.push(p[next - 4] | p[next - 3] << 8 | p[next - 2] << 16 | p[next - 1] << 24);
        break;
      case 'POP': S.pop(); break;
      case 'DUP': S.push(S[S.length - 1]); break;
      case 'SWAP': { const t = S[S.length - 1]; S[S.length - 1] = S[S.length - 2]; S[S.length - 2] = t; break; }
      case 'OVER': S.push(S[S.length - 2]); break;
      case 'ROT': S.push(S.splice(S.length - 3, 1)[0]); break;
      case 'NEG': S[S.length - 1] = -S[S.length - 1] | 0; break;
      case 'NOT': S[S.length - 1] = ~S[S.length - 1]; break;
      case 'ADD': case 'SUB': case 'MUL': case 'DIV': case 'MOD': case 'DIVU': case 'MODU':
      case 'AND': case 'OR': case 'XOR': case 'SHL': case 'SHR': case 'SHRU': case 'EQ': case 'LT': case 'LTU': {
        const b = S.pop()!, a = S.pop()!;
        let r: number;
        switch (name) {
          case 'ADD': r = a + b | 0; break;
          case 'SUB': r = a - b | 0; break;
          case 'MUL': r = Math.imul(a, b); break;
          case 'DIV': r = b === 0 ? 0 : a === -2147483648 && b === -1 ? a : Math.trunc(a / b) | 0; break;
          case 'MOD': r = b === 0 ? 0 : b === -1 ? 0 : a % b | 0; break;
          case 'DIVU': r = b === 0 ? 0 : Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 'MODU': r = b === 0 ? 0 : (a >>> 0) % (b >>> 0) | 0; break;
          case 'AND': r = a & b; break;
          case 'OR': r = a | b; break;
          case 'XOR': r = a ^ b; break;
          case 'SHL': r = a << (b & 31); break;
          case 'SHR': r = a >> (b & 31); break;
          case 'SHRU': r = (a >>> (b & 31)) | 0; break;
          case 'EQ': r = a === b ? 1 : 0; break;
          case 'LT': r = a < b ? 1 : 0; break;
          default: r = a >>> 0 < b >>> 0 ? 1 : 0; // LTU
        }
        if (b === 0 && (name === 'DIV' || name === 'MOD' || name === 'DIVU' || name === 'MODU')) return end(4);
        S.push(r);
        break;
      }
      case 'JMP': case 'JZ': case 'JNZ': {
        const rel = (p[next - 2] | p[next - 1] << 8) << 16 >> 16;
        if (name === 'JMP' || (name === 'JZ' ? S.pop()! === 0 : S.pop()! !== 0)) pc = next + rel;
        break;
      }
      case 'CALL':
        if (C.length === 64) return end(7); // call stack full
        C.push(next);
        pc = p[next - 2] | p[next - 1] << 8;
        break;
      case 'RET':
        if (C.length === 0) return end(8); // call stack empty
        pc = C.pop()!;
        break;
      case 'LOAD': {
        const a = S[S.length - 1];
        if (a < 0 || a > 255) return end(6);
        S[S.length - 1] = M[a];
        break;
      }
      case 'STORE': {
        const a = S[S.length - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = S[S.length - 2];
        S.length -= 2;
        break;
      }
      case 'PRINT': {
        const s = String(S.pop());
        if (out.length + s.length > 65536) return end(11); // output limit
        for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
        break;
      }
      case 'PUTC':
        if (out.length === 65536) return end(11); // output limit
        out.push(S.pop()! & 255);
        break;
      case 'IN': S.push(ip < inp.length ? inp[ip++] : -1); break;
      case 'EXIT': return end(S.pop()! & 255);
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
