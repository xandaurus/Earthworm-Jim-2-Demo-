"use strict";
// Звуковой движок: Z80 + YM2612 + SN76489, воспроизведение через WebAudio. Автор: Alexander Orel
const SND=(()=>{
// Zilog Z80 interpreter (documented + common undocumented behaviour). bus: read(a), write(a,v), in(p), out(p,v)
const S = 0x80, Z = 0x40, Y = 0x20, H = 0x10, X = 0x08, PV = 0x04, N = 0x02, CF = 0x01;
const PAR = new Uint8Array(256); for (let i = 0; i < 256; i++) { let p = 1, v = i; while (v) { p ^= v & 1; v >>= 1; } PAR[i] = p ? PV : 0; }

class Z80 {
  constructor(bus) {
    this.bus = bus; this.r = new Uint8Array(8); this.f = 0;   // r: B C D E H L - A
    this.ar = new Uint8Array(8); this.af_ = 0;                 // shadow regs (B' C' D' E' H' L' - A') and F'
    this.ix = 0; this.iy = 0; this.sp = 0xFFFF; this.pc = 0; this.i = 0; this.rr = 0;
    this.iff1 = 0; this.iff2 = 0; this.im = 0; this.halted = false; this.cycles = 0; this.irqLine = false; this.eiPending = false;
  }
  reset() { this.r.fill(0); this.ar.fill(0); this.f = 0; this.af_ = 0; this.ix = this.iy = 0; this.sp = 0xFFFF; this.pc = 0; this.i = 0; this.rr = 0; this.iff1 = this.iff2 = 0; this.im = 0; this.halted = false; this.irqLine = false; this.eiPending = false; }
  get bc() { return (this.r[0] << 8) | this.r[1]; } set bc(v) { this.r[0] = v >> 8; this.r[1] = v; }
  get de() { return (this.r[2] << 8) | this.r[3]; } set de(v) { this.r[2] = v >> 8; this.r[3] = v; }
  get hl() { return (this.r[4] << 8) | this.r[5]; } set hl(v) { this.r[4] = v >> 8; this.r[5] = v; }
  get af() { return (this.r[7] << 8) | this.f; } set af(v) { this.r[7] = v >> 8; this.f = v & 0xFF; }
  rb(a) { return this.bus.read(a & 0xFFFF); }
  wb(a, v) { this.bus.write(a & 0xFFFF, v & 0xFF); }
  rw(a) { return this.rb(a) | (this.rb(a + 1) << 8); }
  ww(a, v) { this.wb(a, v); this.wb(a + 1, v >> 8); }
  fetch() { const v = this.rb(this.pc); this.pc = (this.pc + 1) & 0xFFFF; return v; }
  fetch16() { const l = this.fetch(); return l | (this.fetch() << 8); }
  push(v) { this.sp = (this.sp - 2) & 0xFFFF; this.ww(this.sp, v); }
  pop() { const v = this.rw(this.sp); this.sp = (this.sp + 2) & 0xFFFF; return v; }
  rp(i) { return i === 0 ? this.bc : i === 1 ? this.de : i === 2 ? this.hl : this.sp; }
  setrp(i, v) { v &= 0xFFFF; if (i === 0) this.bc = v; else if (i === 1) this.de = v; else if (i === 2) this.hl = v; else this.sp = v; }
  getr(i, idx, d) {   // 8-bit operand; idx: ix/iy prefix mode ('ix' | 'iy' | null), d = displacement
    if (i === 6) return this.rb(idx ? this.xy(idx) + d : this.hl);
    if (idx && (i === 4 || i === 5)) { const v = idx === 'ix' ? this.ix : this.iy; return i === 4 ? v >> 8 : v & 0xFF; }
    return this.r[i];
  }
  setr(i, v, idx, d) {
    v &= 0xFF;
    if (i === 6) { this.wb(idx ? this.xy(idx) + d : this.hl, v); return; }
    if (idx && (i === 4 || i === 5)) { let o = idx === 'ix' ? this.ix : this.iy; o = i === 4 ? (o & 0xFF) | (v << 8) : (o & 0xFF00) | v; if (idx === 'ix') this.ix = o; else this.iy = o; return; }
    this.r[i] = v;
  }
  xy(idx) { return idx === 'ix' ? this.ix : this.iy; }
  cc(i) { const f = this.f; switch (i) { case 0: return !(f & Z); case 1: return !!(f & Z); case 2: return !(f & CF); case 3: return !!(f & CF); case 4: return !(f & PV); case 5: return !!(f & PV); case 6: return !(f & S); default: return !!(f & S); } }
  // ---- ALU
  alu(op, b) {
    const a = this.r[7]; let r, f;
    switch (op) {
      case 0: case 1: { const c = op === 1 && (this.f & CF) ? 1 : 0; r = a + b + c; f = ((r & 0xFF) & (S | Y | X)) | (((a ^ b ^ r) & H)) | ((((a ^ r) & (b ^ r)) & 0x80) ? PV : 0) | (r > 0xFF ? CF : 0); break; }
      case 2: case 3: case 7: { const c = op === 3 && (this.f & CF) ? 1 : 0; r = a - b - c; f = ((r & 0xFF) & (S | Y | X)) | (((a ^ b ^ r) & H)) | ((((a ^ b) & (a ^ r)) & 0x80) ? PV : 0) | N | (r < 0 ? CF : 0); if (op === 7) f = (f & ~(Y | X)) | (b & (Y | X)); break; }
      case 4: r = a & b; f = (r & (S | Y | X)) | H | PAR[r & 0xFF]; break;
      case 5: r = a ^ b; f = (r & (S | Y | X)) | PAR[r & 0xFF]; break;
      default: r = a | b; f = (r & (S | Y | X)) | PAR[r & 0xFF];
    }
    r &= 0xFF; if (r === 0 && op !== 7) f |= Z; if (op === 7) { if (((a - b) & 0xFF) === 0) f |= Z; } else if (r === 0) f |= Z;
    if (op === 7) { f &= ~(S); if (((a - b) & 0x80)) f |= S; } else { f = (f & ~S) | (r & S); }
    this.f = f; if (op !== 7) this.r[7] = r;
  }
  inc8(v) { const r = (v + 1) & 0xFF; this.f = (this.f & CF) | (r & (S | Y | X)) | (r === 0 ? Z : 0) | ((v & 0xF) === 0xF ? H : 0) | (v === 0x7F ? PV : 0); return r; }
  dec8(v) { const r = (v - 1) & 0xFF; this.f = (this.f & CF) | (r & (S | Y | X)) | (r === 0 ? Z : 0) | ((v & 0xF) === 0 ? H : 0) | (v === 0x80 ? PV : 0) | N; return r; }
  add16(a, b) { const r = a + b; this.f = (this.f & (S | Z | PV)) | ((r >> 8) & (Y | X)) | (((a ^ b ^ r) >> 8) & H) | (r > 0xFFFF ? CF : 0); return r & 0xFFFF; }
  adc16(a, b) { const c = this.f & CF; const r = a + b + c; this.f = ((r >> 8) & (S | Y | X)) | ((r & 0xFFFF) === 0 ? Z : 0) | (((a ^ b ^ r) >> 8) & H) | ((((a ^ r) & (b ^ r)) & 0x8000) ? PV : 0) | (r > 0xFFFF ? CF : 0); return r & 0xFFFF; }
  sbc16(a, b) { const c = this.f & CF; const r = a - b - c; this.f = ((r >> 8) & (S | Y | X)) | ((r & 0xFFFF) === 0 ? Z : 0) | (((a ^ b ^ r) >> 8) & H) | ((((a ^ b) & (a ^ r)) & 0x8000) ? PV : 0) | N | (r < 0 ? CF : 0); return r & 0xFFFF; }
  rot(t, v) {   // CB rotates/shifts: 0 RLC 1 RRC 2 RL 3 RR 4 SLA 5 SRA 6 SLL 7 SRL
    let c, r; const cin = this.f & CF;
    switch (t) {
      case 0: c = v >> 7; r = ((v << 1) | c) & 0xFF; break;
      case 1: c = v & 1; r = (v >> 1) | (c << 7); break;
      case 2: c = v >> 7; r = ((v << 1) | cin) & 0xFF; break;
      case 3: c = v & 1; r = (v >> 1) | (cin << 7); break;
      case 4: c = v >> 7; r = (v << 1) & 0xFF; break;
      case 5: c = v & 1; r = (v >> 1) | (v & 0x80); break;
      case 6: c = v >> 7; r = ((v << 1) | 1) & 0xFF; break;
      default: c = v & 1; r = v >> 1;
    }
    this.f = (r & (S | Y | X)) | (r === 0 ? Z : 0) | PAR[r] | c; return r;
  }
  daa() {
    let a = this.r[7], c = this.f & CF, add = 0;
    if ((this.f & H) || (a & 0xF) > 9) add |= 6;
    if (c || a > 0x99) { add |= 0x60; c = CF; }
    const r = (this.f & N) ? (a - add) & 0xFF : (a + add) & 0xFF;
    const h = (this.f & N) ? ((this.f & H) && (a & 0xF) < 6 ? H : 0) : ((a & 0xF) > 9 ? H : 0);
    this.f = (r & (S | Y | X)) | (r === 0 ? Z : 0) | h | PAR[r] | (this.f & N) | c; this.r[7] = r;
  }
  // ---- interrupts
  interrupt() {
    this.halted = false; this.iff1 = this.iff2 = 0;
    this.push(this.pc);
    if (this.im === 2) { this.pc = this.rw((this.i << 8) | 0xFF); this.cycles += 19; } else { this.pc = 0x38; this.cycles += 13; }
  }
  step() {
    if (this.irqLine && this.iff1 && !this.eiPending) { this.interrupt(); return; }
    this.eiPending = false;
    if (this.halted) { this.cycles += 4; return; }
    this.rr = (this.rr + 1) & 0x7F;
    let op = this.fetch(), idx = null;
    if (op === 0xDD || op === 0xFD) { idx = op === 0xDD ? 'ix' : 'iy'; op = this.fetch(); this.cycles += 4; if (op === 0xDD || op === 0xFD) { this.pc = (this.pc - 1) & 0xFFFF; return; } }
    const x = op >> 6, y = (op >> 3) & 7, z = op & 7, p = y >> 1, q = y & 1;
    if (op === 0xED) { this.ed(); return; }
    if (op === 0xCB) { this.cb(idx); return; }
    let d = 0;
    const needD = () => { if (idx) d = (this.fetch() << 24) >> 24; };
    switch (x) {
      case 0:
        switch (z) {
          case 0:
            if (y === 0) { this.cycles += 4; }
            else if (y === 1) { const t = (this.r[7] << 8) | this.f; this.r[7] = this.af_ >> 8; this.f = this.af_ & 0xFF; this.af_ = t; this.cycles += 4; }
            else if (y === 2) { const e = (this.fetch() << 24) >> 24; this.cycles += 8; this.r[0]--; if (this.r[0] !== 0) { this.pc = (this.pc + e) & 0xFFFF; this.cycles += 5; } }
            else if (y === 3) { const e = (this.fetch() << 24) >> 24; this.pc = (this.pc + e) & 0xFFFF; this.cycles += 12; }
            else { const e = (this.fetch() << 24) >> 24; this.cycles += 7; if (this.cc(y - 4)) { this.pc = (this.pc + e) & 0xFFFF; this.cycles += 5; } }
            break;
          case 1:
            if (!q) { const v = this.fetch16(); if (p === 2 && idx) { if (idx === 'ix') this.ix = v; else this.iy = v; } else this.setrp(p, v); this.cycles += 10; }
            else { const a = p === 2 && idx ? this.xy(idx) : this.rp(p === 2 ? 2 : p); const b = p === 2 ? a : this.rp(p); const hlv = idx ? this.xy(idx) : this.hl; const r = this.add16(hlv, p === 2 ? hlv : this.rp(p)); if (idx) { if (idx === 'ix') this.ix = r; else this.iy = r; } else this.hl = r; this.cycles += 11; }
            break;
          case 2:
            if (p === 0) { if (!q) this.wb(this.bc, this.r[7]); else this.r[7] = this.rb(this.bc); this.cycles += 7; }
            else if (p === 1) { if (!q) this.wb(this.de, this.r[7]); else this.r[7] = this.rb(this.de); this.cycles += 7; }
            else if (p === 2) { const a = this.fetch16(); if (!q) this.ww(a, idx ? this.xy(idx) : this.hl); else { const v = this.rw(a); if (idx) { if (idx === 'ix') this.ix = v; else this.iy = v; } else this.hl = v; } this.cycles += 16; }
            else { const a = this.fetch16(); if (!q) this.wb(a, this.r[7]); else this.r[7] = this.rb(a); this.cycles += 13; }
            break;
          case 3: {
            if (p === 2 && idx) { const v = (this.xy(idx) + (q ? -1 : 1)) & 0xFFFF; if (idx === 'ix') this.ix = v; else this.iy = v; }
            else this.setrp(p, this.rp(p) + (q ? -1 : 1));
            this.cycles += 6; break;
          }
          case 4: { needD(); const v = this.getr(y, idx, d); this.setr(y, this.inc8(v), idx, d); this.cycles += y === 6 ? (idx ? 19 : 11) : 4; break; }
          case 5: { needD(); const v = this.getr(y, idx, d); this.setr(y, this.dec8(v), idx, d); this.cycles += y === 6 ? (idx ? 19 : 11) : 4; break; }
          case 6: { needD(); const n = this.fetch(); this.setr(y, n, idx, d); this.cycles += y === 6 ? (idx ? 15 : 10) : 7; break; }
          default: {
            const a = this.r[7]; let c; this.cycles += 4;
            switch (y) {
              case 0: c = a >> 7; this.r[7] = ((a << 1) | c) & 0xFF; this.f = (this.f & (S | Z | PV)) | (this.r[7] & (Y | X)) | c; break;
              case 1: c = a & 1; this.r[7] = (a >> 1) | (c << 7); this.f = (this.f & (S | Z | PV)) | (this.r[7] & (Y | X)) | c; break;
              case 2: c = a >> 7; this.r[7] = ((a << 1) | (this.f & CF)) & 0xFF; this.f = (this.f & (S | Z | PV)) | (this.r[7] & (Y | X)) | c; break;
              case 3: c = a & 1; this.r[7] = (a >> 1) | ((this.f & CF) << 7); this.f = (this.f & (S | Z | PV)) | (this.r[7] & (Y | X)) | c; break;
              case 4: this.daa(); break;
              case 5: this.r[7] = a ^ 0xFF; this.f = (this.f & (S | Z | PV | CF)) | (this.r[7] & (Y | X)) | H | N; break;
              case 6: this.f = (this.f & (S | Z | PV)) | (a & (Y | X)) | CF; break;
              default: this.f = (this.f & (S | Z | PV)) | (a & (Y | X)) | ((this.f & CF) ? H : 0) | ((this.f & CF) ? 0 : CF); break;
            }
          }
        }
        break;
      case 1:
        if (y === 6 && z === 6) { this.halted = true; this.cycles += 4; break; }
        needD();
        if (y === 6) { this.setr(6, this.r[z], idx, d); this.cycles += idx ? 19 : 7; }
        else if (z === 6) { this.r[y] = this.getr(6, idx, d); this.cycles += idx ? 19 : 7; }
        else { this.setr(y, this.getr(z, idx, d), idx, d); this.cycles += 4; }
        break;
      case 2: needD(); this.alu(y, this.getr(z, idx, d)); this.cycles += z === 6 ? (idx ? 19 : 7) : 4; break;
      default:
        switch (z) {
          case 0: this.cycles += 5; if (this.cc(y)) { this.pc = this.pop(); this.cycles += 6; } break;
          case 1:
            if (!q) { const v = this.pop(); if (p === 3) this.af = v; else if (p === 2 && idx) { if (idx === 'ix') this.ix = v; else this.iy = v; } else this.setrp(p, v); this.cycles += 10; }
            else if (p === 0) { this.pc = this.pop(); this.cycles += 10; }
            else if (p === 1) { for (let i = 0; i < 6; i++) { const t = this.r[i]; this.r[i] = this.ar[i]; this.ar[i] = t; } this.cycles += 4; }
            else if (p === 2) { this.pc = idx ? this.xy(idx) : this.hl; this.cycles += 4; }
            else { this.sp = idx ? this.xy(idx) : this.hl; this.cycles += 6; }
            break;
          case 2: { const a = this.fetch16(); if (this.cc(y)) this.pc = a; this.cycles += 10; break; }
          case 3:
            if (y === 0) { this.pc = this.fetch16(); this.cycles += 10; }
            else if (y === 2) { const n = this.fetch(); this.bus.out((this.r[7] << 8) | n, this.r[7]); this.cycles += 11; }
            else if (y === 3) { const n = this.fetch(); this.r[7] = this.bus.in((this.r[7] << 8) | n); this.cycles += 11; }
            else if (y === 4) { const v = this.rw(this.sp); const hv = idx ? this.xy(idx) : this.hl; this.ww(this.sp, hv); if (idx) { if (idx === 'ix') this.ix = v; else this.iy = v; } else this.hl = v; this.cycles += 19; }
            else if (y === 5) { const t = this.de; this.de = this.hl; this.hl = t; this.cycles += 4; }
            else if (y === 6) { this.iff1 = this.iff2 = 0; this.cycles += 4; }
            else { this.iff1 = this.iff2 = 1; this.eiPending = true; this.cycles += 4; }
            break;
          case 4: { const a = this.fetch16(); this.cycles += 10; if (this.cc(y)) { this.push(this.pc); this.pc = a; this.cycles += 7; } break; }
          case 5:
            if (!q) { this.push(p === 3 ? this.af : p === 2 && idx ? this.xy(idx) : this.rp(p)); this.cycles += 11; }
            else { const a = this.fetch16(); this.push(this.pc); this.pc = a; this.cycles += 17; }
            break;
          case 6: this.alu(y, this.fetch()); this.cycles += 7; break;
          default: this.push(this.pc); this.pc = y * 8; this.cycles += 11;
        }
    }
  }
  cb(idx) {
    let d = 0; if (idx) d = (this.fetch() << 24) >> 24;
    const op = this.fetch(); const x = op >> 6, y = (op >> 3) & 7, z = op & 7;
    const mem = idx || z === 6; const v = idx ? this.rb(this.xy(idx) + d) : this.getr(z);
    let r;
    if (x === 0) { r = this.rot(y, v); }
    else if (x === 1) {
      const b = v & (1 << y); this.f = (this.f & CF) | H | (b ? 0 : (Z | PV)) | (y === 7 && b ? S : 0) | ((mem ? (idx ? (this.xy(idx) + d) >> 8 : this.hl >> 8) : v) & (Y | X));
      this.cycles += mem ? (idx ? 20 : 12) : 8; return;
    } else if (x === 2) r = v & ~(1 << y); else r = v | (1 << y);
    if (idx) { this.wb(this.xy(idx) + d, r); if (z !== 6) this.r[z] = r; this.cycles += 23; }
    else if (z === 6) { this.wb(this.hl, r); this.cycles += 15; } else { this.r[z] = r; this.cycles += 8; }
  }
  ed() {
    const op = this.fetch(); const x = op >> 6, y = (op >> 3) & 7, z = op & 7, p = y >> 1, q = y & 1;
    if (x === 1) {
      switch (z) {
        case 0: { const v = this.bus.in(this.bc); if (y !== 6) this.r[y] = v; this.f = (this.f & CF) | (v & (S | Y | X)) | (v === 0 ? Z : 0) | PAR[v]; this.cycles += 12; break; }
        case 1: this.bus.out(this.bc, y === 6 ? 0 : this.r[y]); this.cycles += 12; break;
        case 2: this.hl = q ? this.adc16(this.hl, this.rp(p)) : this.sbc16(this.hl, this.rp(p)); this.cycles += 15; break;
        case 3: { const a = this.fetch16(); if (!q) this.ww(a, this.rp(p)); else this.setrp(p, this.rw(a)); this.cycles += 20; break; }
        case 4: { const a = this.r[7]; this.r[7] = 0; this.f = 0; this.alu(2, a); this.cycles += 4; break; }
        case 5: this.pc = this.pop(); this.iff1 = this.iff2; this.cycles += 14; break;
        case 6: this.im = [0, 0, 1, 2, 0, 0, 1, 2][y]; this.cycles += 8; break;
        default:
          switch (y) {
            case 0: this.i = this.r[7]; this.cycles += 9; break;
            case 1: this.rr = this.r[7]; this.cycles += 9; break;
            case 2: this.r[7] = this.i; this.f = (this.f & CF) | (this.r[7] & (S | Y | X)) | (this.r[7] === 0 ? Z : 0) | (this.iff2 ? PV : 0); this.cycles += 9; break;
            case 3: this.r[7] = this.rr; this.f = (this.f & CF) | (this.r[7] & (S | Y | X)) | (this.r[7] === 0 ? Z : 0) | (this.iff2 ? PV : 0); this.cycles += 9; break;
            case 4: { const a = this.r[7], m = this.rb(this.hl); this.r[7] = (a & 0xF0) | (m & 0xF); this.wb(this.hl, ((m >> 4) & 0xF) | ((a & 0xF) << 4)); this.f = (this.f & CF) | (this.r[7] & (S | Y | X)) | (this.r[7] === 0 ? Z : 0) | PAR[this.r[7]]; this.cycles += 18; break; }
            case 5: { const a = this.r[7], m = this.rb(this.hl); this.r[7] = (a & 0xF0) | ((m >> 4) & 0xF); this.wb(this.hl, ((m << 4) & 0xF0) | (a & 0xF)); this.f = (this.f & CF) | (this.r[7] & (S | Y | X)) | (this.r[7] === 0 ? Z : 0) | PAR[this.r[7]]; this.cycles += 18; break; }
            default: this.cycles += 8;
          }
      }
      return;
    }
    if (x === 2 && y >= 4 && z < 4) { this.block(y - 4, z); return; }
    this.cycles += 8;
  }
  block(k, z) {   // k: 0 inc,1 dec,2 inc+repeat,3 dec+repeat ; z 0 LD 1 CP 2 IN 3 OUT
    const dec = k & 1, rep = k >> 1; const dlt = dec ? -1 : 1;
    if (z === 0) {
      const v = this.rb(this.hl); this.wb(this.de, v); this.hl = this.hl + dlt; this.de = this.de + dlt; const bc = (this.bc - 1) & 0xFFFF; this.bc = bc;
      const n = (v + this.r[7]) & 0xFF; this.f = (this.f & (S | Z | CF)) | (n & X) | ((n & 2) ? Y : 0) | (bc ? PV : 0);
      this.cycles += 16; if (rep && bc) { this.pc = (this.pc - 2) & 0xFFFF; this.cycles += 5; }
    } else if (z === 1) {
      const v = this.rb(this.hl); const a = this.r[7]; const r = (a - v) & 0xFF; this.hl = this.hl + dlt; const bc = (this.bc - 1) & 0xFFFF; this.bc = bc;
      const h = ((a ^ v ^ r) & H) ? 1 : 0; const n = r - h;
      this.f = (this.f & CF) | (r & S) | (r === 0 ? Z : 0) | (h ? H : 0) | (bc ? PV : 0) | N | (n & X) | ((n & 2) ? Y : 0);
      this.cycles += 16; if (rep && bc && r !== 0) { this.pc = (this.pc - 2) & 0xFFFF; this.cycles += 5; }
    } else if (z === 2) {
      const v = this.bus.in(this.bc); this.wb(this.hl, v); this.hl = this.hl + dlt; this.r[0] = (this.r[0] - 1) & 0xFF;
      this.f = (this.f & CF) | (this.r[0] === 0 ? Z : 0) | N; this.cycles += 16; if (rep && this.r[0]) { this.pc = (this.pc - 2) & 0xFFFF; this.cycles += 5; }
    } else {
      const v = this.rb(this.hl); this.r[0] = (this.r[0] - 1) & 0xFF; this.bus.out(this.bc, v); this.hl = this.hl + dlt;
      this.f = (this.f & CF) | (this.r[0] === 0 ? Z : 0) | N; this.cycles += 16; if (rep && this.r[0]) { this.pc = (this.pc - 2) & 0xFFFF; this.cycles += 5; }
    }
  }
  runUntil(t) { while (this.cycles < t) this.step(); }
}
// YM2612 (OPN2) – 6 channels x 4 operators, DAC, timers, LFO. One generate() call = one output sample (clock/144).
const SIN = new Float32Array(1024); for (let i = 0; i < 1024; i++) SIN[i] = Math.sin((i + 0.5) / 1024 * 2 * Math.PI);
const EXP = new Float32Array(1024 * 2); for (let i = 0; i < 2048; i++) EXP[i] = Math.pow(2, -i / 64);   // env units: 1/64 octave
const EGINC = [0,1,0,1,0,1,0,1, 0,1,0,1,1,1,0,1, 0,1,1,1,0,1,1,1, 0,1,1,1,1,1,1,1,
  1,1,1,1,1,1,1,1, 1,1,1,2,1,1,1,2, 1,2,1,2,1,2,1,2, 1,2,2,2,1,2,2,2,
  2,2,2,2,2,2,2,2, 2,2,2,4,2,2,2,4, 2,4,2,4,2,4,2,4, 2,4,4,4,2,4,4,4,
  4,4,4,4,4,4,4,4, 4,4,4,8,4,4,4,8, 4,8,4,8,4,8,4,8, 4,8,8,8,4,8,8,8,
  8,8,8,8,8,8,8,8];
const DT = [null,
  [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,2,3,3,3,4,4,4,5,5,6,6,7,8,8,8,8],
  [1,1,1,1,2,2,2,2,2,3,3,3,4,4,4,5,5,6,6,7,8,8,9,10,11,12,13,14,16,16,16,16],
  [2,2,2,2,2,3,3,3,4,4,4,5,5,6,6,7,8,8,9,10,11,12,13,14,16,17,19,20,22,22,22,22]];
const LFO_PER = [108, 77, 71, 67, 62, 44, 8, 5];
const AMS_SH = [8, 3, 1, 0];
const FMS = [0, 3.4, 6.7, 10, 14, 20, 40, 80];   // cents peak
const OPMAP = [0, 2, 1, 3];                          // register slot offset -> operator index
// states
const ATT = 0, DEC = 1, SUS = 2, REL = 3, OFF = 4;

class Op {
  constructor() { this.dt = 0; this.mul = 1; this.tl = 0; this.ks = 0; this.ar = 0; this.am = 0; this.d1r = 0; this.d2r = 0; this.d1l = 0; this.rr = 0; this.ssg = 0;
    this.ph = 0; this.inc = 0; this.env = 1023; this.state = OFF; this.key = 0; this.o = 0; this.o1 = 0; this.cnt = 0; this.rate = 0; this.sl = 0; }
}
class YM2612 {
  constructor() { this.reset(); }
  reset() {
    this.regs = [new Uint8Array(256), new Uint8Array(256)];
    this.op = []; for (let c = 0; c < 6; c++) { const a = []; for (let o = 0; o < 4; o++) a.push(new Op()); this.op.push(a); }
    this.fn = new Uint16Array(6); this.blk = new Uint8Array(6); this.fb = new Uint8Array(6); this.alg = new Uint8Array(6);
    this.pan = new Uint8Array(6).fill(3); this.ams = new Uint8Array(6); this.fms = new Uint8Array(6);
    this.ch3fn = new Uint16Array(4); this.ch3blk = new Uint8Array(4); this.mode3 = 0;
    this.latch = [0, 0]; this.dacEn = 0; this.dac = 0;
    this.ta = 0; this.tb = 0; this.taCnt = 0; this.tbCnt = 0; this.taOn = 0; this.tbOn = 0; this.taEn = 0; this.tbEn = 0; this.status = 0;
    this.egTimer = 0; this.egCnt = 0; this.lfoOn = 0; this.lfoFreq = 0; this.lfoCnt = 0; this.lfoPos = 0;
    this.sub = 0; this.chOut = new Float32Array(6);
  }
  read() { return this.status; }
  write(port, v) {
    v &= 0xFF;
    if (!(port & 1)) { this.latch[port >> 1] = v; return; }
    const part = port >> 1, a = this.latch[part]; this.regs[part][a] = v;
    if (part === 0 && a < 0x30) return this.sys(a, v);
    if (a < 0x30) return;
    let ch = a & 3; if (ch === 3) return; ch += part * 3;
    const o = OPMAP[(a >> 2) & 3], op = this.op[ch][o];
    switch (a & 0xF0) {
      case 0x30: op.dt = (v >> 4) & 7; op.mul = v & 15; this.updInc(ch); break;
      case 0x40: op.tl = v & 0x7F; break;
      case 0x50: op.ks = v >> 6; op.ar = v & 31; break;
      case 0x60: op.am = v >> 7; op.d1r = v & 31; break;
      case 0x70: op.d2r = v & 31; break;
      case 0x80: op.d1l = v >> 4; op.rr = v & 15; op.sl = op.d1l === 15 ? 0x3E0 : op.d1l << 5; break;
      case 0x90: op.ssg = v & 15; break;
      case 0xA0: case 0xB0: this.chreg(part, a, v); break;
    }
  }
  chreg(part, a, v) {
    const c = a & 3; if (c === 3) return; const ch = c + part * 3;
    switch (a) {
      case 0xA0: case 0xA1: case 0xA2: case 0x1A0: break;
    }
    const lo = a & 0xFC;
    if (lo === 0xA0) { this.fn[ch] = ((this.hi || 0) << 8) | v; this.fn[ch] = ((this.hiv[part][c] & 7) << 8) | v; this.blk[ch] = (this.hiv[part][c] >> 3) & 7; this.updInc(ch); }
    else if (lo === 0xA4) { this.hiv[part][c] = v; }
    else if (lo === 0xA8) { if (part === 0) { const i = [2, 0, 1][c]; this.ch3fn[i] = ((this.ch3hi[c] & 7) << 8) | v; this.ch3blk[i] = (this.ch3hi[c] >> 3) & 7; this.updInc(2); } }
    else if (lo === 0xAC) { if (part === 0) this.ch3hi[c] = v; }
    else if (lo === 0xB0) { if (a < 0xB4) { this.fb[ch] = (v >> 3) & 7; this.alg[ch] = v & 7; } else { this.pan[ch] = v >> 6; this.ams[ch] = (v >> 4) & 3; this.fms[ch] = v & 7; } }
  }
  sys(a, v) {
    switch (a) {
      case 0x22: this.lfoOn = (v >> 3) & 1; this.lfoFreq = v & 7; if (!this.lfoOn) { this.lfoPos = 0; this.lfoCnt = 0; } break;
      case 0x24: this.ta = (this.ta & 3) | (v << 2); break;
      case 0x25: this.ta = (this.ta & 0x3FC) | (v & 3); break;
      case 0x26: this.tb = v; break;
      case 0x27: {
        if ((v & 1) && !this.taOn) this.taCnt = 1024 - this.ta; this.taOn = v & 1;
        if ((v & 2) && !this.tbOn) this.tbCnt = (256 - this.tb) * 16; this.tbOn = (v >> 1) & 1;
        this.taEn = (v >> 2) & 1; this.tbEn = (v >> 3) & 1;
        if (v & 0x10) this.status &= ~1; if (v & 0x20) this.status &= ~2;
        const m = (v >> 6) & 3; if (m !== this.mode3) { this.mode3 = m; this.updInc(2); } break;
      }
      case 0x28: {
        let c = v & 7; if ((c & 3) === 3) return; if (c >= 4) c--;
        for (let o = 0; o < 4; o++) this.keyOp(this.op[c][o], (v >> (4 + o)) & 1, c);
        break;
      }
      case 0x2A: this.dac = v; break;
      case 0x2B: this.dacEn = v >> 7; break;
    }
  }
  keyOp(op, on, ch) {
    if (on && !op.key) { op.ph = 0; op.state = ATT; this.rateCalc(op, ch); if (this.arRate(op, ch) >= 62) { op.env = 0; op.state = DEC; } }
    else if (!on && op.key) { if (op.state !== OFF) op.state = REL; }
    op.key = on;
  }
  kc(ch, o) { const fn = (this.mode3 && ch === 2) ? this.ch3fn[o] : this.fn[ch]; const bl = (this.mode3 && ch === 2) ? this.ch3blk[o] : this.blk[ch];
    const f11 = (fn >> 10) & 1, f10 = (fn >> 9) & 1, f9 = (fn >> 8) & 1, f8 = (fn >> 7) & 1; const n3 = (f11 & (f10 | f9 | f8)) | ((!f11 ? 1 : 0) & f10 & f9 & f8);
    return (bl << 2) | (f11 << 1) | n3; }
  arRate(op, ch) { return op.ar ? Math.min(63, 2 * op.ar + (this.kcOf(ch, op) >> (3 - op.ks))) : 0; }
  kcOf(ch, op) { return this.op[ch].indexOf(op) >= 0 ? this.kc(ch, this.op[ch].indexOf(op)) : 0; }
  rateCalc(op, ch) { }
  updInc(ch) {
    for (let o = 0; o < 4; o++) {
      const op = this.op[ch][o]; const sp = this.mode3 && ch === 2;
      const fn = sp ? this.ch3fn[o] : this.fn[ch], bl = sp ? this.ch3blk[o] : this.blk[ch];
      let inc = (fn << bl) >> 1; const kc = this.kc(ch, o); const d = DT[op.dt & 3] ? DT[op.dt & 3][kc] : 0; inc += (op.dt & 4) ? -d : d; if (inc < 0) inc += 0x20000; inc &= 0x1FFFF;
      op.inc = op.mul ? inc * op.mul : inc >> 1; op.kc = kc;
    }
  }
  egRate(op, r) { // r: effective rate 0..63 for state step
    return r;
  }
  stepEnv(ch) {
    const cnt = this.egCnt;
    for (let o = 0; o < 4; o++) {
      const op = this.op[ch][o]; if (op.state === OFF && !op.key) continue;
      const kcs = op.kc >> (3 - op.ks);
      let R;
      switch (op.state) {
        case ATT: R = op.ar ? Math.min(63, 2 * op.ar + kcs) : 0; break;
        case DEC: R = op.d1r ? Math.min(63, 2 * op.d1r + kcs) : 0; break;
        case SUS: R = op.d2r ? Math.min(63, 2 * op.d2r + kcs) : 0; break;
        default: R = Math.min(63, 4 * op.rr + 2 + kcs);
      }
      if (R < 2) continue;
      let sh = 11 - (R >> 2); if (sh < 0) sh = 0;
      if (cnt & ((1 << sh) - 1)) continue;
      let row; if (R < 48) row = R & 3; else if (R < 60) row = 4 + (R - 48); else row = 16; // rows of 8
      let inc = EGINC[row * 8 + ((cnt >> sh) & 7)];
      if (op.state === ATT) {
        if (R >= 62) { op.env = 0; } else op.env += ((~op.env) * inc) >> 4;
        if (op.env <= 0) { op.env = 0; op.state = DEC; }
      } else if (op.state === DEC) {
        op.env += inc; if (op.env >= op.sl) { op.env = op.sl; op.state = SUS; }
      } else if (op.state === SUS) { op.env += inc; if (op.env > 1023) op.env = 1023; }
      else { op.env += inc; if (op.env >= 1023) { op.env = 1023; op.state = OFF; } }
    }
  }
  opOut(op, pm, ch, lfoAm) {
    let e = op.env + (op.tl << 3); if (op.am) e += lfoAm >> AMS_SH[this.ams[ch]]; if (this.ams[ch] === 0 && op.am) e -= lfoAm >> AMS_SH[0]; if (e > 1023) e = 1023;
    if (e < 0) e = 0;
    const idx = ((op.ph >> 10) + (pm | 0)) & 1023;
    return SIN[idx] * EXP[e] * 4095;
  }
  generate() {   // returns [L,R] in this.l / this.r (about +-32768 for full-scale single channel*..)
    // timers (one tick per sample)
    if (this.taOn && --this.taCnt <= 0) { this.taCnt = 1024 - this.ta; if (this.taEn) this.status |= 1; }
    if (this.tbOn && --this.tbCnt <= 0) { this.tbCnt = (256 - this.tb) * 16; if (this.tbEn) this.status |= 2; }
    // envelope clock every 3 samples
    if (++this.egTimer >= 3) { this.egTimer = 0; this.egCnt = (this.egCnt + 1) & 0xFFF; for (let c = 0; c < 6; c++) this.stepEnv(c); }
    // LFO
    let lfoAm = 0, lfoPm = 0;
    if (this.lfoOn) {
      if (++this.lfoCnt >= LFO_PER[this.lfoFreq]) { this.lfoCnt = 0; this.lfoPos = (this.lfoPos + 1) & 127; }
      const p = this.lfoPos; lfoAm = (p < 64 ? p : 127 - p) * 2; lfoPm = Math.sin(p / 128 * 2 * Math.PI);
    }
    let L = 0, R = 0;
    for (let c = 0; c < 6; c++) {
      const ops = this.op[c], o1 = ops[0], o2 = ops[1], o3 = ops[2], o4 = ops[3];
      let vib = 1; if (this.lfoOn && this.fms[c]) vib = Math.pow(2, FMS[this.fms[c]] * lfoPm / 1200);
      for (let o = 0; o < 4; o++) { const op = ops[o]; op.ph = (op.ph + (vib === 1 ? op.inc : op.inc * vib)) % 1048576; }
      const O1 = this.opOut(o1, this.fb[c] ? (o1.o + o1.o1) / (1 << (10 - this.fb[c])) : 0, c, lfoAm);
      o1.o1 = o1.o; o1.o = O1;
      let out = 0, m;
      const h = x => x / 2;  // modulation index
      switch (this.alg[c]) {
        case 0: { const a2 = this.opOut(o2, h(O1), c, lfoAm), a3 = this.opOut(o3, h(a2), c, lfoAm); out = this.opOut(o4, h(a3), c, lfoAm); break; }
        case 1: { const a2 = this.opOut(o2, 0, c, lfoAm), a3 = this.opOut(o3, h(O1 + a2), c, lfoAm); out = this.opOut(o4, h(a3), c, lfoAm); break; }
        case 2: { const a2 = this.opOut(o2, 0, c, lfoAm), a3 = this.opOut(o3, h(a2), c, lfoAm); out = this.opOut(o4, h(O1 + a3), c, lfoAm); break; }
        case 3: { const a2 = this.opOut(o2, h(O1), c, lfoAm), a3 = this.opOut(o3, 0, c, lfoAm); out = this.opOut(o4, h(a2 + a3), c, lfoAm); break; }
        case 4: { const a2 = this.opOut(o2, h(O1), c, lfoAm), a4 = this.opOut(o4, h(this.opOut(o3, 0, c, lfoAm)), c, lfoAm); out = a2 + a4; break; }
        case 5: { const a2 = this.opOut(o2, h(O1), c, lfoAm), a3 = this.opOut(o3, h(O1), c, lfoAm), a4 = this.opOut(o4, h(O1), c, lfoAm); out = a2 + a3 + a4; break; }
        case 6: { const a2 = this.opOut(o2, h(O1), c, lfoAm), a3 = this.opOut(o3, 0, c, lfoAm), a4 = this.opOut(o4, 0, c, lfoAm); out = a2 + a3 + a4; break; }
        default: { out = O1 + this.opOut(o2, 0, c, lfoAm) + this.opOut(o3, 0, c, lfoAm) + this.opOut(o4, 0, c, lfoAm); }
      }
      if (c === 5 && this.dacEn) out = (this.dac - 128) * 32;
      out *= 3;   // ~ +-12k per full channel
      const p = this.pan[c]; if (p & 2) L += out; if (p & 1) R += out;
    }
    this.l = L; this.r = R;
  }
}
YM2612.prototype.hiv = null;
const _ctor = YM2612.prototype.reset;
YM2612.prototype.reset = function () { _ctor.call(this); this.hiv = [new Uint8Array(4), new Uint8Array(4)]; this.ch3hi = new Uint8Array(4); };
// SN76489 PSG (Sega variant: 16-bit LFSR, white noise taps bit0^bit3). Clocked at Z80 clock (master/15), divide-by-16.
class PSG {
  constructor() { this.reset(); }
  reset() {
    this.tone = new Uint16Array([1, 1, 1, 1]);      // [0..2] tone dividers, [3] noise control (low 3 bits)
    this.vol = new Uint8Array([15, 15, 15, 15]);
    this.cnt = new Int32Array(4); this.out = new Int8Array(4).fill(1);
    this.lfsr = 0x8000; this.latch = 0; this.frac = 0;
    this.LV = new Float32Array(16); for (let i = 0; i < 15; i++) this.LV[i] = Math.pow(10, -2 * i / 20); this.LV[15] = 0;
  }
  write(v) {
    if (v & 0x80) {
      this.latch = (v >> 4) & 7; const ch = this.latch >> 1;
      if (this.latch & 1) this.vol[ch] = v & 15;
      else if (ch === 3) { this.tone[3] = v & 7; this.lfsr = 0x8000; }
      else this.tone[ch] = (this.tone[ch] & 0x3F0) | (v & 15);
    } else {
      const ch = this.latch >> 1;
      if (this.latch & 1) this.vol[ch] = v & 15;
      else if (ch === 3) { this.tone[3] = v & 7; this.lfsr = 0x8000; }
      else this.tone[ch] = (this.tone[ch] & 15) | ((v & 0x3F) << 4);
    }
  }
  tick() {   // one divide-by-16 step
    for (let c = 0; c < 3; c++) {
      if (--this.cnt[c] <= 0) { this.cnt[c] = this.tone[c] || 1024; this.out[c] = -this.out[c]; }
    }
    if (--this.cnt[3] <= 0) {
      const nf = this.tone[3] & 3; this.cnt[3] = nf === 3 ? (this.tone[2] || 1024) * 1 : (16 << nf);
      // noise flips every 2*cnt in real chip; flip output on each reload
      this.nout = !this.nout;
      if (this.nout) {
        const fb = (this.tone[3] & 4) ? ((this.lfsr ^ (this.lfsr >> 3)) & 1) : (this.lfsr & 1);
        this.lfsr = (this.lfsr >> 1) | (fb << 15); this.out[3] = (this.lfsr & 1) ? 1 : -1;
      }
    }
  }
  // returns mono sample in about [-1,1]*0.5, averaging ticks that elapse in 'ticksPerSample'
  sample(tps) {
    this.frac += tps; let n = this.frac | 0; this.frac -= n; if (n < 1) n = 1; // always >=1
    let s = 0;
    for (let i = 0; i < n; i++) {
      this.tick();
      for (let c = 0; c < 4; c++) s += this.out[c] * this.LV[this.vol[c]];
    }
    return s / n * 0.18;
  }
}

// ---- Звук (N6): Z80 + YM2612 + PSG; драйвер и данные — из ROM пользователя (личное использование)
const SND=(()=>{
 const BASE=SNDDATA.base, bin=Uint8Array.from(atob(SNDDATA.b64),c=>c.charCodeAt(0));
 const rom=new Uint8Array(0x300000); rom.set(bin,BASE);
 const zram=new Uint8Array(0x2000); zram.set(rom.subarray(0x277BC8,0x277BC8+0x1886),0);
 const ym=new YM2612(), psg=new PSG(); let bank=0, now=0, ymSamples=0, tzOver=-1, cyc=0;
 const RATE=7600489/144, PSGT=(144*7/15)/16, RING=1<<14, buf=new Int16Array(RING*2); let wpos=0, rpos=0;
 const nowC=()=>tzOver>=0?tzOver:cyc;
 function syncYM(){ const target=Math.floor(nowC()/144); while(ymSamples<target){ ym.generate(); const p=psg.sample(PSGT)*8000; let l=ym.l+p,r=ym.r+p; l=l>32767?32767:l<-32768?-32768:l; r=r>32767?32767:r<-32768?-32768:r; const i=(wpos&(RING-1))*2; buf[i]=l;buf[i+1]=r;wpos++;ymSamples++; } }
 const zr=a=>{ if(a<0x4000)return zram[a&0x1FFF]; if(a<0x6000){syncYM();return ym.read();} if(a<0x8000)return 0xFF; const ad=(bank<<15)|(a&0x7FFF); return ad<0x300000?rom[ad]:0xFF; };
 const zw=(a,v)=>{ if(a<0x4000){zram[a&0x1FFF]=v;return;} if(a<0x6000){syncYM();ym.write(a&3,v);return;} if(a<0x6100){bank=((bank>>1)|((v&1)<<8))&0x1FF;return;} if(a===0x7F11){syncYM();psg.write(v);} };
 const z=new Z80({read:zr,write:zw,in:()=>0xFF,out:()=>{}});
 let widx=0; const pending=[];
 const push=b=>{ for(const x of [0xFF,...b]){ zram[0x1B40+widx]=x; widx=(widx+1)&63; zram[0x36]=widx; } };
 const FR=152744;   // кадр PAL в тактах 68000
 function runZ(t){ const tz=t*7/15; while(z.cycles<tz){ tzOver=Math.floor(z.cycles*15/7); z.step(); } tzOver=-1; }
 function frame(){ while(pending.length)push(pending.shift()); const t0=cyc; z.irqLine=true; cyc=t0+488; runZ(cyc); z.irqLine=false; cyc=t0+FR; runZ(cyc); syncYM(); }
 let ctx=null, node=null, started=false, pk=0, calls=0;
 function init(){ // сброс Z80 и команда инициализации драйвера (пакет из лога оригинала)
  z.reset(); push([11,78,148,39,188,161,39,188,161,39,1,84,40]); for(let i=0;i<5;i++)frame(); rpos=wpos; }
 function start(music){ if(started)return; started=true;
  try{ ctx=new (window.AudioContext||window.webkitAudioContext)(); }catch(e){ return; }
  init(); if(music!=null)play(music);
  const sr=ctx.sampleRate, step=RATE/sr; let pos=0, prev=[0,0];
  node=ctx.createScriptProcessor(2048,0,2);
  node.onaudioprocess=e=>{ calls++; const L=e.outputBuffer.getChannelData(0), R=e.outputBuffer.getChannelData(1);
   for(let i=0;i<L.length;i++){ while(wpos-rpos<4){ frame(); if(wpos-rpos>RING-8192)rpos=wpos-4096; }
    const p=rpos&(RING-1), q=(rpos+1)&(RING-1), f=pos-Math.floor(pos);
    L[i]=(buf[p*2]+(buf[q*2]-buf[p*2])*f)/32768*0.8; R[i]=(buf[p*2+1]+(buf[q*2+1]-buf[p*2+1])*f)/32768*0.8;
    {const a=Math.abs(L[i]);if(a>pk)pk=a;} pos+=step; const k=Math.floor(pos); pos-=k; rpos+=k; } };
  node.connect(ctx.destination); if(ctx.state==='suspended')ctx.resume(); }
 function play(id){ pending.push([18,id],[16,id]); }
 let muted=false;function mute(){muted=!muted;if(ctx)muted?ctx.suspend():ctx.resume()}
 return {start,play,mute,get ctx(){return ctx},get on(){return started}, stat:()=>({ctx:ctx&&ctx.state,wpos,rpos,pk,calls})};
})();

return SND;})();

