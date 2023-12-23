use core::fmt;
use core::cmp;

use yaxpeax_arch::{AddressDiff, Arch, Decoder, LengthedInstruction, Reader, StandardDecodeError};

#[derive(Debug)]
pub struct RX;

impl Arch for RX {
    type Address = u32;
    type Word = u8;
    type Instruction = Instruction;
    type DecodeError = StandardDecodeError;
    type Decoder = InstDecoder;
    type Operand = Operand;
}

#[derive(Debug)]
pub struct Instruction {
    opcode: Opcode,
    operands: [Operand; 3],
    length: u8,
}

impl Instruction {
    pub fn opcode(&self) -> Opcode {
        self.opcode
    }

    pub fn operands(&self) -> &[Operand] {
        &self.operands[..self.operand_count() as usize]
    }

    pub fn length(&self) -> u8 {
        self.length
    }

    fn operand_count(&self) -> u8 {
        let mut operands = 0;
        for op in self.operands.iter() {
            if op == &Operand::Nothing {
                return operands;
            }
            operands += 1;
        }

        operands
    }
}

impl Default for Instruction {
    fn default() -> Instruction {
        Instruction {
            opcode: Opcode::NOP,
            operands: [Operand::Nothing, Operand::Nothing, Operand::Nothing],
            length: 1,
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.opcode())?;
        let ops = self.operands();
        if ops[0] != Operand::Nothing {
            write!(f, " {}", ops[0])?;
        }
        if ops[1] != Operand::Nothing {
            write!(f, ", {}", ops[1])?;
        }
        if ops[2] != Operand::Nothing {
            write!(f, ", {}", ops[2])?;
        }
        Ok(())
    }
}

impl LengthedInstruction for Instruction {
    type Unit = AddressDiff<<RX as Arch>::Address>;
    fn min_size() -> Self::Unit {
        AddressDiff::from_const(1)
    }
    fn len(&self) -> Self::Unit {
        AddressDiff::from_const(self.length as u32)
    }
}

impl yaxpeax_arch::Instruction for Instruction {
    // only know how to decode well-formed instructions at the moment
    fn well_defined(&self) -> bool { true }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum PSWBit {
    C,
    Z,
    S,
    O,
    I,
    U,
}

impl fmt::Display for PSWBit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PSWBit::C => f.write_str("c"),
            PSWBit::Z => f.write_str("z"),
            PSWBit::S => f.write_str("s"),
            PSWBit::O => f.write_str("o"),
            PSWBit::I => f.write_str("i"),
            PSWBit::U => f.write_str("u"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ControlReg {
    PSW,
    PC,
    USP,
    FPSW,
    BPSW,
    BPC,
    ISP,
    FINTV,
    INTB,
    EXTB,
    DPSW,
    DCMR,
    DECNT,
    DEPC,
}

impl fmt::Display for ControlReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ControlReg::PSW => f.write_str("psw"),
            ControlReg::PC => f.write_str("pc"),
            ControlReg::USP => f.write_str("usp"),
            ControlReg::FPSW => f.write_str("fpsw"),
            ControlReg::BPSW => f.write_str("bpsw"),
            ControlReg::BPC => f.write_str("bpc"),
            ControlReg::ISP => f.write_str("isp"),
            ControlReg::FINTV => f.write_str("fintv"),
            ControlReg::INTB => f.write_str("intb"),
            ControlReg::EXTB => f.write_str("extb"),
            ControlReg::DPSW => f.write_str("dpsw"),
            ControlReg::DCMR => f.write_str("dcmr"),
            ControlReg::DECNT => f.write_str("decnt"),
            ControlReg::DEPC => f.write_str("DEPC")
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct BitfieldSpec {
    bits: u16,
}

impl fmt::Display for BitfieldSpec {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#{}, #{}, #{}", self.source_start_bit(), self.destination_start_bit(), self.width())
    }
}

impl BitfieldSpec {
    /// the least-significant bit to start moving from the source operand. this is also described
    /// as `slsb` in the `rx` manuals.
    fn source_start_bit(&self) -> u8 {
        let dslb_and_slsb = ((self.bits >> 10) & 0b11111) as u8;
        self.destination_start_bit().wrapping_sub(dslb_and_slsb) & 0x1f
    }

    /// the least-significant bit to start moving into in the destination operand. this is also
    /// described as `dlsb` in the `rx` manuals.
    fn destination_start_bit(&self) -> u8 {
        ((self.bits >> 5) & 0b11111) as u8
    }

    /// the number of bits to move from the source operand to the destination operand.
    fn width(&self) -> u8 {
        let dslb_and_width = ((self.bits >> 10) & 0b11111) as u8;
        dslb_and_width.wrapping_sub(self.destination_start_bit()) & 0x1f
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Operand {
    Nothing,
    /// one of the 16 32-bit general purpose registers: `R0 (sp)` through `R15`.
    Register { num: u8 },
    /// a range of registers, from `start_gpr` to `end_gpr`
    RegisterRange { start_gpr: u8, end_gpr: u8 },
    /// one of the 16 32-bit general purpose registers, but a smaller part of it. typically
    /// sign-extended to 32b for processing.
    Subreg { num: u8, width: SizeCode },
    Accumulator { num: u8 },
    /// `bfmov` and `bfmovz`, textually, describe the bitfield to be moved with three parameters.
    /// those three parameters are expressed as this one operand.
    BitfieldSpec { bf_spec: BitfieldSpec },
    /// one of the 16 64-bit double-precision floating point registers: `DR0` through `DR15`.
    DoubleReg { num: u8 },
    DoubleRegLow { num: u8 },
    DoubleRegHigh { num: u8 },
    ControlReg { reg: ControlReg },
    PSWBit { bit: PSWBit },
    Deref { gpr: u8, disp: u32, width: SizeCode },
    DerefIndexed { base: u8, index: u8, width: SizeCode },
    DoubleRegisterRange { start_reg: u8, end_reg: u8 },
    DoubleControlRegisterRange { start_reg: u8, end_reg: u8 },
    BrS(u8),
    ImmB { imm: u8 },
    ImmW { imm: u16 },
    /// a 24-bit immediate. this is used as a branch offset, and is treated as a sign-extended
    /// 24-bit value, so it is represented as that extended form here.
    BrA { offset: i32 },
    ImmL { imm: u32 },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SizeCode {
    B,
    W,
    L,
    D,
    UW,
}

impl SizeCode {
    fn bytes(&self) -> u8 {
        match self {
            SizeCode::B => 1,
            SizeCode::W => 2,
            SizeCode::UW => 2,
            SizeCode::L => 4,
            SizeCode::D => 8,
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operand::Nothing => {
                f.write_str("")
            },
            Operand::Register { num } => {
                write!(f, "r{}", num)
            },
            Operand::RegisterRange { start_gpr, end_gpr } => {
                write!(f, "r{}-r{}", start_gpr, end_gpr)
            }
            Operand::Subreg { num, width: _unused } => {
                // the width of this register is communicated, textually, by a suffix on the
                // mnemonic...
                write!(f, "r{}", num)
            }
            Operand::Accumulator { num } => {
                write!(f, "a{}", num)
            },
            Operand::BitfieldSpec { bf_spec } => {
                fmt::Display::fmt(bf_spec, f)
            }
            Operand::DoubleReg { num } => {
                write!(f, "dr{}", num)
            },
            Operand::DoubleRegLow { num } => {
                write!(f, "drl{}", num)
            },
            Operand::DoubleRegHigh { num } => {
                write!(f, "drh{}", num)
            },
            Operand::ControlReg { reg } => {
                fmt::Display::fmt(reg, f)
            },
            Operand::PSWBit { bit } => {
                fmt::Display::fmt(bit, f)
            }
            Operand::Deref { gpr, disp, .. } => {
                if *disp == 0 {
                    write!(f, "[r{}]", gpr)
                } else {
                    write!(f, "{}[r{}]", disp, gpr)
                }
            },
            Operand::DerefIndexed { base, index, .. } => {
                // `ri` *is* scaled by the size of the access, but this is communicated as a suffix
                // on the instruction...
                write!(f, "[r{}, r{}]", base, index)
            }
            Operand::DoubleRegisterRange { start_reg, end_reg } => {
                write!(f, "dr{}-dr{}", start_reg, end_reg)
            }
            Operand::DoubleControlRegisterRange { start_reg, end_reg } => {
                // TODO: give the control registers names...
                write!(f, "dcr{}-dcr{}", start_reg, end_reg)
            }
            Operand::BrS(disp) => {
                // a short branch `disp` bytes forward
                write!(f, "$+{}", disp)
            }
            Operand::BrA { offset } => {
                // a branch by signed `offset` bytes
                write!(f, "$+{}", offset)
            }
            Operand::ImmB { imm } => {
                write!(f, "#{}", imm)
            }
            Operand::ImmW { imm } => {
                write!(f, "#{}", imm)
            }
            Operand::ImmL { imm } => {
                write!(f, "#{}", imm)
            }
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Opcode {
    REVW,
    REVL,
    MSBHI,
    MSBLH,
    MSBLO,
    EMSBA,
    MVFACHI,
    MVFACLO,
    MVFACMI,
    MVFACGU,
    RACW,
    RACL,
    RDACW,
    RDACL,
    MVTACHI,
    MVTACLO,
    MVTACGU,
    XOR,
    OR,
    AND,
    MUL,
    ADD,
    SUB,
    MOVU,
    SHLL,
    SHAR,
    SHLR,
    BRA,
    NOP,
    MOV,
    DMOV,
    ROTR,
    ROTL,
    SCEQ,
    SCNE,
    SCGEU,
    SCLTU,
    SCGTU,
    SCLEU,
    SCPZ,
    SCN,
    SCGE,
    SCLT,
    SCGT,
    SCLE,
    SCO,
    SCNO,
    BMEQ,
    BMNE,
    BMGEU,
    BMLTU,
    BMGTU,
    BMLEU,
    BMPZ,
    BMN,
    BMGE,
    BMLT,
    BMGT,
    BMLE,
    BMO,
    BMNO,
    BNOT,
    FSUB,
    FCMP,
    FADD,
    FMUL,
    FDIV,
    MVFC,
    MVFDC,
    MVTC,
    MVTDC,
    STNZ,
    STZ,
    TST,
    DIVU,
    DIV,
    EMULU,
    EMUL,
    MIN,
    MAX,
    ITOD,
    FTOD,
    UTOD,
    ADC,
    RSTR,
    SAVE,
    MULHI,
    MULLO,
    MULLH,
    EMULA,
    MACHI,
    MACLO,
    MACLH,
    EMACA,
    FTOI,
    ITOF,
    FTOU,
    UTOF,
    FSQRT,
    ROUND,
    BSET,
    BCLR,
    BTST,
    BFMOV,
    BFMOVZ,
    ABS,
    NOT,
    XCHG,
    SBB,
    RTFI,
    RTE,
    WAIT,
    SETPSW,
    CLRPSW,
    RMPA_B,
    RMPA_W,
    RMPA_L,
    SMOVF,
    SATR,
    SSTR_B,
    SSTR_W,
    SSTR_L,
    SMOVB,
    SWHILE_B,
    SWHILE_W,
    SWHILE_L,
    SMOVU,
    SUNTIL_B,
    SUNTIL_W,
    SUNTIL_L,
    SCMPU,
    JMP,
    JSR,
    POP,
    POPC,
    POPM,
    PUSH,
    PUSHC,
    PUSHM,
    RORC,
    ROLC,
    NEG,
    DPUSHM,
    DPOP,
    DTOF,
    DROUND,
    DSQRT,
    DTOI,
    DTOU,
    DABS,
    DNEG,
    DADD,
    DSUB,
    DMUL,
    DDIV,
    DCMPUN,
    DCMPEQ,
    DCMPLT,
    DCMPLE,
    INT,
    MVTIPL,
    MVFDR,
    CMP,
    SAT,
    RTSD,
    BSR,
    BRK,
    BEQ,
    BNE,
    BGEU,
    BLTU,
    BGTU,
    BLEU,
    BPZ,
    BN,
    BGE,
    BLT,
    BGT,
    BLE,
    BO,
    BNO,
    RTS,
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Opcode::REVW => f.write_str("revw"),
            Opcode::REVL => f.write_str("revl"),
            Opcode::MSBHI => f.write_str("msbhi"),
            Opcode::MSBLH => f.write_str("msblh"),
            Opcode::MSBLO => f.write_str("msblo"),
            Opcode::EMSBA => f.write_str("emsba"),
            Opcode::MVFACHI => f.write_str("mvfachi"),
            Opcode::MVFACLO => f.write_str("mvfaclo"),
            Opcode::MVFACMI => f.write_str("mvfacmi"),
            Opcode::MVFACGU => f.write_str("mvfacgu"),
            Opcode::RACW => f.write_str("racw"),
            Opcode::RACL => f.write_str("racl"),
            Opcode::RDACW => f.write_str("rdacw"),
            Opcode::RDACL => f.write_str("rdacl"),
            Opcode::MVTACHI => f.write_str("mvtachi"),
            Opcode::MVTACLO => f.write_str("mvtaclo"),
            Opcode::MVTACGU => f.write_str("mvtacgu"),
            Opcode::XOR => f.write_str("xor"),
            Opcode::OR => f.write_str("or"),
            Opcode::AND => f.write_str("and"),
            Opcode::MUL => f.write_str("mul"),
            Opcode::ADD => f.write_str("add"),
            Opcode::SUB => f.write_str("sub"),
            Opcode::MOVU => f.write_str("movu"),
            Opcode::SHLL => f.write_str("shll"),
            Opcode::SHAR => f.write_str("shar"),
            Opcode::SHLR => f.write_str("shlr"),
            Opcode::BRA => f.write_str("bra"),
            Opcode::NOP => f.write_str("nop"),
            Opcode::MOV => f.write_str("mov"),
            Opcode::DMOV => f.write_str("dmov"),
            Opcode::ROTR => f.write_str("rotr"),
            Opcode::ROTL => f.write_str("rotl"),
            Opcode::SCEQ => f.write_str("sceq"),
            Opcode::SCNE => f.write_str("scne"),
            Opcode::SCGEU => f.write_str("scgeu"),
            Opcode::SCLTU => f.write_str("scltu"),
            Opcode::SCGTU => f.write_str("scgtu"),
            Opcode::SCLEU => f.write_str("scleu"),
            Opcode::SCPZ => f.write_str("scpz"),
            Opcode::SCN => f.write_str("scn"),
            Opcode::SCGE => f.write_str("scge"),
            Opcode::SCLT => f.write_str("sclt"),
            Opcode::SCGT => f.write_str("scgt"),
            Opcode::SCLE => f.write_str("scle"),
            Opcode::SCO => f.write_str("sco"),
            Opcode::SCNO => f.write_str("scno"),
            Opcode::BMEQ => f.write_str("bmeq"),
            Opcode::BMNE => f.write_str("bmne"),
            Opcode::BMGEU => f.write_str("bmgeu"),
            Opcode::BMLTU => f.write_str("bmltu"),
            Opcode::BMGTU => f.write_str("bmgtu"),
            Opcode::BMLEU => f.write_str("bmleu"),
            Opcode::BMPZ => f.write_str("bmpz"),
            Opcode::BMN => f.write_str("bmn"),
            Opcode::BMGE => f.write_str("bmge"),
            Opcode::BMLT => f.write_str("bmlt"),
            Opcode::BMGT => f.write_str("bmgt"),
            Opcode::BMLE => f.write_str("bmle"),
            Opcode::BMO => f.write_str("bmo"),
            Opcode::BMNO => f.write_str("bmno"),
            Opcode::BNOT => f.write_str("bnot"),
            Opcode::FSUB => f.write_str("fsub"),
            Opcode::FCMP => f.write_str("fcmp"),
            Opcode::FADD => f.write_str("fadd"),
            Opcode::FMUL => f.write_str("fmul"),
            Opcode::FDIV => f.write_str("fdiv"),
            Opcode::MVFC => f.write_str("mvfc"),
            Opcode::MVFDC => f.write_str("mvfdc"),
            Opcode::MVTC => f.write_str("mvtc"),
            Opcode::MVTDC => f.write_str("mvtdc"),
            Opcode::STNZ => f.write_str("stnz"),
            Opcode::STZ => f.write_str("stz"),
            Opcode::TST => f.write_str("tst"),
            Opcode::DIVU => f.write_str("divu"),
            Opcode::DIV => f.write_str("div"),
            Opcode::EMULU => f.write_str("emulu"),
            Opcode::EMUL => f.write_str("emul"),
            Opcode::MIN => f.write_str("min"),
            Opcode::MAX => f.write_str("max"),
            Opcode::ITOD => f.write_str("itod"),
            Opcode::FTOD => f.write_str("ftod"),
            Opcode::UTOD => f.write_str("utod"),
            Opcode::ADC => f.write_str("adc"),
            Opcode::RSTR => f.write_str("rstr"),
            Opcode::SAVE => f.write_str("save"),
            Opcode::MULHI => f.write_str("mulhi"),
            Opcode::MULLO => f.write_str("mullo"),
            Opcode::MULLH => f.write_str("mullh"),
            Opcode::EMULA => f.write_str("emula"),
            Opcode::MACHI => f.write_str("machi"),
            Opcode::MACLO => f.write_str("maclo"),
            Opcode::MACLH => f.write_str("maclh"),
            Opcode::EMACA => f.write_str("emaca"),
            Opcode::FTOI => f.write_str("ftoi"),
            Opcode::ITOF => f.write_str("itof"),
            Opcode::FTOU => f.write_str("ftou"),
            Opcode::UTOF => f.write_str("utof"),
            Opcode::FSQRT => f.write_str("fsqrt"),
            Opcode::ROUND => f.write_str("round"),
            Opcode::BSET => f.write_str("bset"),
            Opcode::BCLR => f.write_str("bclr"),
            Opcode::BTST => f.write_str("btst"),
            Opcode::BFMOV => f.write_str("bfmov"),
            Opcode::BFMOVZ => f.write_str("bfmovz"),
            Opcode::ABS => f.write_str("abs"),
            Opcode::NOT => f.write_str("not"),
            Opcode::XCHG => f.write_str("xchg"),
            Opcode::SBB => f.write_str("sbb"),
            Opcode::RTFI => f.write_str("rtfi"),
            Opcode::RTE => f.write_str("rte"),
            Opcode::WAIT => f.write_str("wait"),
            Opcode::SETPSW => f.write_str("setpsw"),
            Opcode::CLRPSW => f.write_str("clrpsw"),
            Opcode::RMPA_B => f.write_str("rmpa_b"),
            Opcode::RMPA_W => f.write_str("rmpa_w"),
            Opcode::RMPA_L => f.write_str("rmpa_l"),
            Opcode::SMOVF => f.write_str("smovf"),
            Opcode::SATR => f.write_str("satr"),
            Opcode::SSTR_B => f.write_str("sstr_b"),
            Opcode::SSTR_W => f.write_str("sstr_w"),
            Opcode::SSTR_L => f.write_str("sstr_l"),
            Opcode::SMOVB => f.write_str("smovb"),
            Opcode::SWHILE_B => f.write_str("swhile_b"),
            Opcode::SWHILE_W => f.write_str("swhile_w"),
            Opcode::SWHILE_L => f.write_str("swhile_l"),
            Opcode::SMOVU => f.write_str("smovu"),
            Opcode::SUNTIL_B => f.write_str("suntil_b"),
            Opcode::SUNTIL_W => f.write_str("suntil_w"),
            Opcode::SUNTIL_L => f.write_str("suntil_l"),
            Opcode::SCMPU => f.write_str("scmpu"),
            Opcode::JMP => f.write_str("jmp"),
            Opcode::JSR => f.write_str("jsr"),
            Opcode::POP => f.write_str("pop"),
            Opcode::POPC => f.write_str("popc"),
            Opcode::POPM => f.write_str("popm"),
            Opcode::PUSH => f.write_str("push"),
            Opcode::PUSHC => f.write_str("pushc"),
            Opcode::PUSHM => f.write_str("pushm"),
            Opcode::RORC => f.write_str("rorc"),
            Opcode::ROLC => f.write_str("rolc"),
            Opcode::NEG => f.write_str("neg"),
            Opcode::DPUSHM => f.write_str("dpushm"),
            Opcode::DPOP => f.write_str("dpop"),
            Opcode::DTOF => f.write_str("dtof"),
            Opcode::DROUND => f.write_str("dround"),
            Opcode::DSQRT => f.write_str("dsqrt"),
            Opcode::DTOI => f.write_str("dtoi"),
            Opcode::DTOU => f.write_str("dtou"),
            Opcode::DABS => f.write_str("dabs"),
            Opcode::DNEG => f.write_str("dneg"),
            Opcode::DADD => f.write_str("dadd"),
            Opcode::DSUB => f.write_str("dsub"),
            Opcode::DMUL => f.write_str("dmul"),
            Opcode::DDIV => f.write_str("ddiv"),
            Opcode::DCMPUN => f.write_str("dcmpun"),
            Opcode::DCMPEQ => f.write_str("dcmpeq"),
            Opcode::DCMPLT => f.write_str("dcmplt"),
            Opcode::DCMPLE => f.write_str("dcmple"),
            Opcode::INT => f.write_str("int"),
            Opcode::MVTIPL => f.write_str("mvtipl"),
            Opcode::MVFDR => f.write_str("mvfdr"),
            Opcode::CMP => f.write_str("cmp"),
            Opcode::SAT => f.write_str("sat"),
            Opcode::RTSD => f.write_str("rtsd"),
            Opcode::BSR => f.write_str("bsr"),
            Opcode::BRK => f.write_str("brk"),
            Opcode::BEQ => f.write_str("beq"),
            Opcode::BNE => f.write_str("bne"),
            Opcode::BGEU => f.write_str("bgeu"),
            Opcode::BLTU => f.write_str("bltu"),
            Opcode::BGTU => f.write_str("bgtu"),
            Opcode::BLEU => f.write_str("bleu"),
            Opcode::BPZ => f.write_str("bpz"),
            Opcode::BN => f.write_str("bn"),
            Opcode::BGE => f.write_str("bge"),
            Opcode::BLT => f.write_str("blt"),
            Opcode::BGT => f.write_str("bgt"),
            Opcode::BLE => f.write_str("ble"),
            Opcode::BO => f.write_str("bo"),
            Opcode::BNO => f.write_str("bno"),
            Opcode::RTS => f.write_str("rts"),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord)]
#[repr(u8)]
pub enum RxVersion {
    V1,
    V2,
    V3,
}

impl PartialOrd for RxVersion {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        (*self as u8).partial_cmp(&(*other as u8))
    }
}

#[test]
fn versions_compare_right() {
    assert!(RxVersion::V1 < RxVersion::V2);
    assert!(RxVersion::V2 < RxVersion::V3);
    assert!(RxVersion::V1 < RxVersion::V3);
}

#[derive(Debug)]
pub struct InstDecoder {
    version: RxVersion,
}

impl Default for InstDecoder {
    fn default() -> Self {
        InstDecoder { version: RxVersion::V3 }
    }
}

impl InstDecoder {
    fn num_to_psw_bit(&self, reg: u8) -> Result<Operand, <RX as Arch>::DecodeError> {
        match reg {
            0b0000 => Ok(Operand::PSWBit { bit: PSWBit::C }),
            0b0001 => Ok(Operand::PSWBit { bit: PSWBit::Z }),
            0b0010 => Ok(Operand::PSWBit { bit: PSWBit::S }),
            0b0011 => Ok(Operand::PSWBit { bit: PSWBit::O }),
            0b1000 => Ok(Operand::PSWBit { bit: PSWBit::I }),
            0b1001 => Ok(Operand::PSWBit { bit: PSWBit::U }),
            _ => Err(StandardDecodeError::InvalidOperand),
        }
    }

    fn reg_to_control_reg(&self, reg: u8) -> Result<Operand, <RX as Arch>::DecodeError> {
        match reg {
            0b0000 => { Ok(Operand::ControlReg { reg: ControlReg::PSW }) },
            0b0001 => { Ok(Operand::ControlReg { reg: ControlReg::PC }) },
            0b0010 => { Ok(Operand::ControlReg { reg: ControlReg::USP }) },
            0b0011 => { Ok(Operand::ControlReg { reg: ControlReg::FPSW}) },
            0b1000 => { Ok(Operand::ControlReg { reg: ControlReg::BPSW }) },
            0b1001 => { Ok(Operand::ControlReg { reg: ControlReg::BPC }) },
            0b1010 => { Ok(Operand::ControlReg { reg: ControlReg::ISP }) },
            0b1011 => { Ok(Operand::ControlReg { reg: ControlReg::FINTV }) },
            0b1100 => { Ok(Operand::ControlReg { reg: ControlReg::INTB }) },
            0b1101 => {
                if self.version >= RxVersion::V3 {
                    Ok(Operand::ControlReg { reg: ControlReg::EXTB })
                } else {
                    Err(StandardDecodeError::InvalidOperand)
                }
            },
            _ => {
                Err(StandardDecodeError::InvalidOperand)
            }
        }
    }

    fn reg_to_double_control_reg(&self, reg: u8) -> Result<Operand, <RX as Arch>::DecodeError> {
        match reg {
            0b0000 => { Ok(Operand::ControlReg { reg: ControlReg::DPSW }) },
            0b0001 => { Ok(Operand::ControlReg { reg: ControlReg::DCMR }) },
            0b0010 => { Ok(Operand::ControlReg { reg: ControlReg::DECNT }) },
            0b0011 => { Ok(Operand::ControlReg { reg: ControlReg::DEPC }) },
            _ => {
                Err(StandardDecodeError::InvalidOperand)
            }
        }
    }
}

trait DecodeHandler<T: Reader<<RX as Arch>::Address, <RX as Arch>::Word>> {
    #[inline(always)]
    fn read_u8(&mut self, words: &mut T) -> Result<u8, <RX as Arch>::DecodeError> {
        let b = words.next()?;
        self.on_word_read(b);
        Ok(b)
    }
    #[inline(always)]
    fn read_u16(&mut self, words: &mut T) -> Result<u16, <RX as Arch>::DecodeError> {
        let mut buf = [0u8; 2];
        words.next_n(&mut buf).ok().ok_or(StandardDecodeError::ExhaustedInput)?;
        self.on_word_read(buf[0]);
        self.on_word_read(buf[1]);
        Ok(u16::from_le_bytes(buf))
    }
    #[inline(always)]
    fn read_u24(&mut self, words: &mut T) -> Result<u32, <RX as Arch>::DecodeError> {
        let mut buf = [0u8; 4];
        // read into a four-byte buffer, filling the low 3 bytes so we can turn this whole thing
        // into a u32 in-place
        words.next_n(&mut buf[1..4]).ok().ok_or(StandardDecodeError::ExhaustedInput)?;
        self.on_word_read(buf[0]);
        self.on_word_read(buf[1]);
        self.on_word_read(buf[2]);
        Ok(u32::from_le_bytes(buf))
    }
    #[inline(always)]
    fn read_i24(&mut self, words: &mut T) -> Result<i32, <RX as Arch>::DecodeError> {
        let v = self.read_u24(words)?;
        Ok(((v as i32) << 8) >> 8)
    }
    #[inline(always)]
    fn read_u32(&mut self, words: &mut T) -> Result<u32, <RX as Arch>::DecodeError> {
        let mut buf = [0u8; 4];
        words.next_n(&mut buf).ok().ok_or(StandardDecodeError::ExhaustedInput)?;
        self.on_word_read(buf[0]);
        self.on_word_read(buf[1]);
        self.on_word_read(buf[2]);
        self.on_word_read(buf[3]);
        Ok(u32::from_le_bytes(buf))
    }
    /// helper to decode the bits for an `ld`-style operand, with variants like "deref", "deref
    /// with displacement", and "deref with larger displacement", into an `Operand`.
    ///
    /// it is not clear how `size` is handled, if at all, for instructions where `ld` would
    /// indicate a register (non-deref). the manual does not indicate that sign or zero extension
    /// of source registers is possible for register-register operand combinations, so the likely
    /// cases are that either size!=L would trap, or is ignored and means full register width
    /// regardless.
    fn decode_mem_op(&mut self, rs: u8, ld: u8, size: SizeCode, words: &mut T) -> Result<Operand, <RX as Arch>::DecodeError> {
        Ok(match ld {
            0b00 => {
                Operand::Deref { gpr: rs, disp: 0, width: size }
            },
            0b01 => {
                let disp = self.read_u8(words)? as u32;
                Operand::Deref { gpr: rs, disp, width: size }
            }
            0b10 => {
                let disp = self.read_u16(words)? as u32;
                Operand::Deref { gpr: rs, disp, width: size }
            }
            _ => {
                // callers (should all be internal) should never pass larger `ld`..
                // it's not clear how ``
                debug_assert!(ld == 0b11);
                Operand::Register { num: rs }
            }
        })
    }
    fn on_decode_start(&mut self) {}
    fn on_decode_end(&mut self) {}
    fn on_opcode_decoded(&mut self, _opcode: Opcode) -> Result<(), <RX as Arch>::DecodeError> { Ok(()) }
    fn on_operand_decoded(&mut self, _number: u8, _operand: Operand) -> Result<(), <RX as Arch>::DecodeError> { Ok(()) }
    fn on_word_read(&mut self, _word: <RX as Arch>::Word) {}
}

impl<T: yaxpeax_arch::Reader<<RX as Arch>::Address, <RX as Arch>::Word>> DecodeHandler<T> for Instruction {
    fn on_decode_start(&mut self) {
        self.length = 0;
        self.opcode = Opcode::NOP;
        self.operands = [Operand::Nothing, Operand::Nothing, Operand::Nothing];
    }
    fn on_opcode_decoded(&mut self, opcode: Opcode) -> Result<(), <RX as Arch>::DecodeError> {
        self.opcode = opcode;
        Ok(())
    }
    fn on_operand_decoded(&mut self, number: u8, operand: Operand) -> Result<(), <RX as Arch>::DecodeError> {
        self.operands[number as usize] = operand;
        Ok(())
    }
    fn on_word_read(&mut self, _word: <RX as Arch>::Word) {
        self.length += 1;
    }
}

impl Decoder<RX> for InstDecoder {
    fn decode_into<T: Reader<<RX as Arch>::Address, <RX as Arch>::Word>>(&self, inst: &mut Instruction, words: &mut T) -> Result<(), <RX as Arch>::DecodeError> {
        decode_inst(self, inst, words)
    }
}

fn decode_inst<
    T: Reader<<RX as Arch>::Address, <RX as Arch>::Word>,
    H: DecodeHandler<T>,
>(decoder: &<RX as Arch>::Decoder, handler: &mut H, words: &mut T) -> Result<(), <RX as Arch>::DecodeError> {
    handler.on_decode_start();

    let opc: u8 = handler.read_u8(words)?;

    if opc == 0b0000_0000 {
        handler.on_opcode_decoded(Opcode::BRK)?;
    } else if opc == 0b0000_0001 {
        return Err(StandardDecodeError::InvalidOpcode);
    } else if opc == 0b0000_0010 {
        handler.on_opcode_decoded(Opcode::RTS)?;
    } else if opc == 0b0000_0011 {
        handler.on_opcode_decoded(Opcode::NOP)?;
    } else if opc == 0b0000_0100 {
        handler.on_opcode_decoded(Opcode::BRA)?;
        let offset = handler.read_i24(words)?;
        handler.on_operand_decoded(0, Operand::BrA { offset })?;
    } else if opc == 0b0000_0101 {
        handler.on_opcode_decoded(Opcode::BSR)?;
        let offset = handler.read_i24(words)?;
        handler.on_operand_decoded(0, Operand::BrA { offset })?;
    } else if opc == 0b0000_0110 {
        let next: u8 = handler.read_u8(words)?;
        let mi = (next >> 6) & 0b11;
        let ld = next & 0b11;
        let opc = (next >> 2) & 0b1111;

        if opc < 0b0110 {
            const OPC_TABLE: [Opcode; 6] = [Opcode::SUB, Opcode::CMP, Opcode::ADD, Opcode::MUL, Opcode::AND, Opcode::OR];

            handler.on_opcode_decoded(OPC_TABLE[opc as usize])?;
        } else if opc == 0b1000 {
            handler.on_opcode_decoded(match next {
                0b0_0000 => {
                    if mi == 0b10 && ld != 0b11 {
                        Opcode::SBB
                    } else {
                        return Err(StandardDecodeError::InvalidOperand);
                    }
                }
                0b0_0001 => {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                0b0_0010 => {
                    if mi == 0b10 && ld != 0b11 {
                        Opcode::ADC
                    } else {
                        return Err(StandardDecodeError::InvalidOperand);
                    }
                }
                0b0_0011 => {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                0b0_0100 => { Opcode::MAX },
                0b0_0101 => { Opcode::MIN },
                0b0_0110 => { Opcode::EMUL },
                0b0_0111 => { Opcode::EMULU },
                0b0_1000 => { Opcode::DIV },
                0b0_1001 => { Opcode::DIVU },
                0b0_1010 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b0_1011 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b0_1100 => { Opcode::TST },
                0b0_1101 => { Opcode::XOR },
                0b0_1110 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b0_1111 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_0000 => { Opcode::XCHG },
                0b1_0001 => { Opcode::ITOF },
                0b1_0010 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_0011 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_0100 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_0101 => if decoder.version >= RxVersion::V2 {
                    Opcode::UTOF
                } else {
                    return Err(StandardDecodeError::InvalidOpcode);
                },
                0b1_0110 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_0111 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1000 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1001 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1010 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1011 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1100 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1101 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1110 => { return Err(StandardDecodeError::InvalidOpcode); },
                0b1_1111 => { return Err(StandardDecodeError::InvalidOpcode); },
                // any of the upper three bits being set here are invalid
                _ => { return Err(StandardDecodeError::InvalidOpcode); },
            })?;
        } else {
            return Err(StandardDecodeError::InvalidOpcode);
        }

        // read operands
        let next: u8 = handler.read_u8(words)?;

        let rs = (next >> 4) & 0b1111;
        let rd = next & 0b1111;

        let size = [SizeCode::B, SizeCode::W, SizeCode::L, SizeCode::UW][mi as usize];
        let src = handler.decode_mem_op(rs, ld, size, words)?;

        handler.on_operand_decoded(0, src)?;
        handler.on_operand_decoded(1, Operand::Register { num: rd })?;
    } else if opc == 0b0000_0111 {
        return Err(StandardDecodeError::InvalidOpcode);
    } else if opc < 0b0001_0000 {
        handler.on_opcode_decoded(Opcode::BRA)?;
        let disp = opc & 0b111;
        // TODO: double-check the displacement offset thingy
        handler.on_operand_decoded(0, Operand::BrS(disp))?;
    } else if opc < 0b0010_0000 {
        handler.on_opcode_decoded(if opc & 0b0000_1000 == 0 {
            Opcode::BEQ
        } else {
            Opcode::BNE
        })?;
        let disp = opc & 0b111;
        // TODO: double-check the displacement offset thingy
        handler.on_operand_decoded(0, Operand::BrS(disp))?;
    } else if opc < 0b0011_0000 {
        // BCnd.B
        let cond = opc & 0b1111;
        const OPC_TABLE: &'static [Opcode] = &[
            Opcode::BEQ, Opcode::BNE, Opcode::BGEU, Opcode::BLTU,
            Opcode::BGTU, Opcode::BLEU, Opcode::BPZ, Opcode::BN,
            Opcode::BGE, Opcode::BLT, Opcode::BGT, Opcode::BLE,
            Opcode::BO, Opcode::BNO, Opcode::BRA, /* no branch for cnd=1111 */
        ];

        if let Some(op) = OPC_TABLE.get(cond as usize) {
            handler.on_opcode_decoded(*op)?;
            let imm = handler.read_u8(words)?;
            handler.on_operand_decoded(0, Operand::ImmB { imm })?;
        } else {
            return Err(StandardDecodeError::InvalidOpcode);
        }
    } else if opc < 0b0011_1000 {
        return Err(StandardDecodeError::InvalidOpcode);
    } else if opc == 0b0011_1000 {
        handler.on_opcode_decoded(Opcode::BRA)?;
        let imm = handler.read_u16(words)?;
        handler.on_operand_decoded(0, Operand::ImmW { imm })?;
    } else if opc == 0b0011_1001 {
        handler.on_opcode_decoded(Opcode::BSR)?;
        let imm = handler.read_u16(words)?;
        handler.on_operand_decoded(0, Operand::ImmW { imm })?;
    } else if opc == 0b0011_1010 {
        handler.on_opcode_decoded(Opcode::BEQ)?;
        let imm = handler.read_u16(words)?;
        handler.on_operand_decoded(0, Operand::ImmW { imm })?;
    } else if opc == 0b0011_1011 {
        handler.on_opcode_decoded(Opcode::BNE)?;
        let imm = handler.read_u16(words)?;
        handler.on_operand_decoded(0, Operand::ImmW { imm })?;
    } else if opc < 0b0011_1111 {
        // MOV.size
        handler.on_opcode_decoded(Opcode::MOV)?;
        let operands = handler.read_u8(words)?;
        let rd = (operands >> 4) & 0b111;
        let disp = (((operands >> 3) & 0b10000) | (operands & 0b1111)) as u8 as u32;
        let imm = handler.read_u8(words)?;
        match opc & 0b11 {
            0b00 => {
                handler.on_operand_decoded(0, Operand::ImmB { imm: imm as u8 })?;
                handler.on_operand_decoded(1, Operand::Deref { gpr: rd, disp, width: SizeCode::B })?;
            }
            0b01 => {
                handler.on_operand_decoded(0, Operand::ImmW { imm: imm as u8 as u16 })?;
                handler.on_operand_decoded(1, Operand::Deref { gpr: rd, disp, width: SizeCode::W })?;
            }
            0b10 => {
                handler.on_operand_decoded(0, Operand::ImmL { imm: imm as u8 as u32 })?;
                handler.on_operand_decoded(1, Operand::Deref { gpr: rd, disp, width: SizeCode::L })?;
            }
            _ => { unreachable!("sz=11 is rtsd") }
        };
    } else if opc == 0b0011_1111 {
        handler.on_opcode_decoded(Opcode::RTSD)?;

        let operands = handler.read_u8(words)?;
        let imm = handler.read_u8(words)?;
        let rd = operands >> 4;
        let rd2 = operands & 0b1111;
        handler.on_operand_decoded(0, Operand::ImmB { imm })?;
        handler.on_operand_decoded(1, Operand::RegisterRange { start_gpr: rd, end_gpr: rd2 })?;
    } else if opc < 0b0110_0000 {
        let code = (opc >> 2) & 0b111;
        let opcode = [
            Opcode::SUB, Opcode::CMP, Opcode::ADD, Opcode::MUL,
            Opcode::AND, Opcode::OR, Opcode::MOVU, Opcode::MOVU,
        ][code as usize];
        handler.on_opcode_decoded(opcode)?;

        let ld = opc & 0b11;
        let operands = handler.read_u8(words)?;
        let rs = operands >> 4;
        let rd = operands & 0b1111;

        let size = [
            SizeCode::L, SizeCode::L, SizeCode::L, SizeCode::L,
            SizeCode::L, SizeCode::L, SizeCode::B, SizeCode::W,
        ][code as usize];
        let src = handler.decode_mem_op(rs, ld, size, words)?;
        handler.on_operand_decoded(0, src)?;
        handler.on_operand_decoded(1, Operand::Register { num: rd })?;
    } else if opc < 0b0111_0000 {
        // 0 1 1 0 ....
        let opc = opc & 0b1111;
        if opc < 0b1000 {
            // 0 1 1 0 0 ...
            // either sub/cmp/add/.. or rtsd
            let operands = handler.read_u8(words)?;
            if opc == 0b0111 {
                handler.on_opcode_decoded(Opcode::RTSD)?;
                handler.on_operand_decoded(0, Operand::ImmB { imm: operands })?;
            } else {
                let imm = operands >> 4;
                let rd = operands & 0b1111;
                handler.on_operand_decoded(0, Operand::ImmB { imm })?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            }
        } else if opc < 0b1110 {
            // 0 1 1 0 1 ...
            handler.on_opcode_decoded(match opc >> 1 {
                0b100 => Opcode::SHLR,
                0b101 => Opcode::SHAR,
                0b110 => Opcode::SHLL,
                _ => { unreachable!("implies opc=0b1111") }
            })?;
            let operands = handler.read_u8(words)?;
            let imm = operands >> 3;
            let rd = operands & 0b111;
            handler.on_operand_decoded(0, Operand::ImmB { imm })?;
            handler.on_operand_decoded(1, Operand::Register { num: rd })?;
        } else {
            // 0 1 1 0 1 1 1 x
            handler.on_opcode_decoded(if opc == 0b1110 {
                Opcode::PUSHM
            } else {
                Opcode::POPM
            })?;
            let operands = handler.read_u8(words)?;
            let reg_lo = operands >> 4;
            let reg_hi = operands & 0b1111;
            handler.on_operand_decoded(0, Operand::RegisterRange { start_gpr: reg_lo, end_gpr: reg_hi })?;
        }
    } else if opc < 0b0111_0100 {
        // 0 1 1 1 0 0 li
        handler.on_opcode_decoded(Opcode::ADD)?;
        let operands = handler.read_u8(words)?;
        let rs2 = operands >> 4;
        let rd = operands & 0b1111;
        let li = opc & 0b11;
        let imm = match li {
            0b00 => {
                handler.read_u32(words)?
            }
            0b01 => {
                handler.read_u8(words)? as i8 as i32 as u32
            }
            0b10 => {
                handler.read_u16(words)? as i16 as i32 as u32
            }
            _ => {
                debug_assert!(li == 0b11, "li is at most the low two bits set");
                handler.read_i24(words)? as u32
            }
        };
        handler.on_operand_decoded(0, Operand::ImmL { imm })?;
        handler.on_operand_decoded(1, Operand::Register { num: rs2 })?;
        handler.on_operand_decoded(2, Operand::Register { num: rd })?;
    } else if opc < 0b0111_1000 {
        // 0 1 1 1 0 1 li
        let li = opc & 0b11;
        let operands = handler.read_u8(words)?;
        let opc = operands >> 4;
        let opcode = match opc {
            0b0000 => Some(Opcode::CMP),
            0b0001 => Some(Opcode::MUL),
            0b0010 => Some(Opcode::AND),
            0b0011 => Some(Opcode::OR),
            0b0100 => {
                if li != 0b01 {
                    return Err(StandardDecodeError::InvalidOperand);
                }
                Some(Opcode::MOV)
            }
            0b0101 => {
                if li != 0b01 {
                    return Err(StandardDecodeError::InvalidOperand);
                }
                Some(Opcode::CMP)
            }
            _ => {
                // might still be a valid instruction, but we don't know the opcode for sure yet.
                // or we might be able to discern the opcode, but operands need extra checking
                // (like `int`).
                None
            }
        };
        let rd = operands & 0b1111;
        let imm = match li {
            0b00 => {
                handler.read_u32(words)?
            }
            0b01 => {
                handler.read_u8(words)? as i8 as i32 as u32
            }
            0b10 => {
                handler.read_u16(words)? as i16 as i32 as u32
            }
            _ => {
                debug_assert!(li == 0b11, "li is at most the low two bits set");
                handler.read_i24(words)? as u32
            }
        };
        if let Some(op) = opcode {
            handler.on_opcode_decoded(op)?;
            handler.on_operand_decoded(0, Operand::ImmL { imm })?;
            handler.on_operand_decoded(1, Operand::Register { num: rd })?;
        } else {
            if opc == 0b0110 {
                // might be `int`, depends on rd
                if rd == 0 {
                    handler.on_opcode_decoded(Opcode::INT)?;
                    handler.on_operand_decoded(0, Operand::ImmB { imm: imm as u8 })?;
                } else {
                    return Err(StandardDecodeError::InvalidOperand);
                }
            } else if opc == 0b0111 {
                // might be `mvitpl`
                if rd == 0 && (imm & 0b1111_0000 == 0) {
                    handler.on_opcode_decoded(Opcode::MVTIPL)?;
                    handler.on_operand_decoded(0, Operand::ImmB { imm: imm as u8 & 0b1111 })?;
                } else {
                    return Err(StandardDecodeError::InvalidOperand);
                }
            } else if opc == 0b1001 {
                // might be `mvfdr`, or other new double-precision instructions
                if decoder.version < RxVersion::V3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                if rd != 0 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                if li == 0b01 {
                    if imm != 0b0001_1011 {
                        handler.on_opcode_decoded(Opcode::MVFDR)?;
                    } else {
                        return Err(StandardDecodeError::InvalidOperand);
                    }
                } else if li == 0b10 {
                    let rs = imm as u8;
                    let rd = (imm >> 4) as u8;
                    let opc = (imm >> 8) as u8;
                    let rs2 = (imm >> 12) as u8;

                    let opcode = match opc {
                        0b0000 => Opcode::DADD,
                        0b0001 => Opcode::DSUB,
                        0b0010 => Opcode::DMUL,
                        /*0011 is invalid*/
                        0b0100 => Opcode::DDIV,
                        /*0101 and 0110 are invalid*/
                        0b0111 => {
                            // unlike others, dcmp has variants selected by `rd`
                            let opc = match rd {
                                0b0001 => Opcode::DCMPUN,
                                0b0010 => Opcode::DCMPEQ,
                                0b0100 => Opcode::DCMPLT,
                                0b0110 => Opcode::DCMPLE,
                                _ => {
                                    return Err(StandardDecodeError::InvalidOpcode);
                                }
                            };
                            handler.on_opcode_decoded(opc)?;
                            handler.on_operand_decoded(0, Operand::DoubleReg { num: rs })?;
                            handler.on_operand_decoded(1, Operand::DoubleReg { num: rs2 })?;
                            return Ok(());
                        }
                        0b1100 => {
                            // dmovd or a few others, depending on "rs"
                            let opc = match rs {
                                0b0000 => Opcode::DMOV,
                                0b0001 => Opcode::DABS,
                                0b0010 => Opcode::DNEG,
                                _ => {
                                    return Err(StandardDecodeError::InvalidOpcode);
                                }
                            };
                            handler.on_opcode_decoded(opc)?;
                            handler.on_operand_decoded(0, Operand::DoubleReg { num: rs })?;
                            handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
                            return Ok(());
                        }
                        0b1101 => {
                            // dsqrt or others, depending on "rs"
                            let opc = match rs {
                                0b0000 => Opcode::DSQRT,
                                0b1000 => Opcode::DTOI,
                                0b1001 => Opcode::DTOU,
                                0b1100 => Opcode::DTOF,
                                0b1101 => Opcode::DROUND,
                                _ => {
                                    return Err(StandardDecodeError::InvalidOpcode);
                                }
                            };
                            handler.on_opcode_decoded(opc)?;
                            handler.on_operand_decoded(0, Operand::DoubleReg { num: rs })?;
                            handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
                            return Ok(());
                        }
                        _ => {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                    };
                    handler.on_opcode_decoded(opcode)?;
                    handler.on_operand_decoded(0, Operand::DoubleReg { num: rs })?;
                    handler.on_operand_decoded(1, Operand::DoubleReg { num: rs2 })?;
                    handler.on_operand_decoded(2, Operand::DoubleReg { num: rd })?;
                } else {
                    return Err(StandardDecodeError::InvalidOperand);
                }
            } else if opc == 0b1010 {
                // dpushm.l/dpopm.l
                let opc = if rd == 0b000 {
                    Opcode::DPUSHM
                } else if rd == 0b1000 {
                    Opcode::DPOP
                } else {
                    return Err(StandardDecodeError::InvalidOperand);
                };
                handler.on_opcode_decoded(opc)?;
                let rs = (imm as u8 >> 4) & 0b1111;
                let nm = imm as u8 & 0b1111;
                let end_reg = rs + nm + 1;
                if end_reg > 15 {
                    return Err(StandardDecodeError::InvalidOperand);
                }
                handler.on_operand_decoded(0, Operand::DoubleControlRegisterRange { start_reg: rs, end_reg })?;
            } else if opc == 0b1011 {
                // dpushm.d/dpopm.d
                let opc = if rd == 0b000 {
                    Opcode::DPUSHM
                } else if rd == 0b1000 {
                    Opcode::DPOP
                } else {
                    return Err(StandardDecodeError::InvalidOperand);
                };
                handler.on_opcode_decoded(opc)?;
                let rs = (imm as u8 >> 4) & 0b1111;
                let nm = imm as u8 & 0b1111;
                let end_reg = rs + nm + 1;
                if end_reg > 15 {
                    return Err(StandardDecodeError::InvalidOperand);
                }
                handler.on_operand_decoded(0, Operand::DoubleRegisterRange { start_reg: rs, end_reg })?;
            } else {
                return Err(StandardDecodeError::InvalidOperand);
            }
        }
    } else if opc < 0b0111_1110 {
        // 0 1 1 1 1 xx _
        // BSET, BCLR, BTST
        let operands = handler.read_u8(words)?;
        let imm = ((opc & 1) << 4) | (operands >> 4);
        let rd = operands & 0b1111;
        let opc = match (operands >> 1) & 0b11 {
            0b00 => Opcode::BSET,
            0b01 => Opcode::BCLR,
            // already tested for opc=11 by the `if` above, this is opc=10
            _ => Opcode::BTST,
        };
        handler.on_opcode_decoded(opc)?;
        handler.on_operand_decoded(0, Operand::ImmB { imm })?;
        handler.on_operand_decoded(1, Operand::Register { num: rd })?;
    } else if opc < 0b0111_1111 {
        // 0 1 1 1 1 1 1 0
        let operands = handler.read_u8(words)?;
        let opc = operands >> 4;
        let rd = operands & 0b1111;
        match opc {
            0b0000 => {
                handler.on_opcode_decoded(Opcode::NOT)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b0001 => {
                handler.on_opcode_decoded(Opcode::NEG)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b0010 => {
                handler.on_opcode_decoded(Opcode::ABS)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b0011 => {
                handler.on_opcode_decoded(Opcode::SAT)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b0100 => {
                handler.on_opcode_decoded(Opcode::RORC)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b0101 => {
                handler.on_opcode_decoded(Opcode::ROLC)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b1000 => {
                handler.on_opcode_decoded(Opcode::PUSH)?;
                handler.on_operand_decoded(0, Operand::Subreg { num: rd, width: SizeCode::B })?;
            }
            0b1001 => {
                handler.on_opcode_decoded(Opcode::PUSH)?;
                handler.on_operand_decoded(0, Operand::Subreg { num: rd, width: SizeCode::W })?;
            }
            0b1010 => {
                handler.on_opcode_decoded(Opcode::PUSH)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b1011 => {
                handler.on_opcode_decoded(Opcode::POP)?;
                handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            }
            0b1100 => {
                handler.on_opcode_decoded(Opcode::PUSHC)?;
                handler.on_operand_decoded(0, decoder.reg_to_control_reg(rd)?)?;
            }
            0b1110 => {
                handler.on_opcode_decoded(Opcode::POPC)?;
                // can't popc into pc
                if rd == 0b0001 {
                    return Err(StandardDecodeError::InvalidOperand);
                }
                handler.on_operand_decoded(0, decoder.reg_to_control_reg(rd)?)?;
            }
            _ => {
                return Err(StandardDecodeError::InvalidOpcode);
            }
        }
    } else if opc < 0b1000_0000 {
        // 0 1 1 1 1 1 1 1
        let operands = handler.read_u8(words)?;
        let opc = operands >> 4;
        if opc < 0b1000 {
            handler.on_operand_decoded(0, Operand::Register { num: operands & 0b1111 })?;
            let opcode = match opc {
                0b0000 => Opcode::JMP,
                0b0001 => Opcode::JSR,
                0b0100 => Opcode::BRA,
                0b0101 => Opcode::BRA,
                _ => {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
            };
            handler.on_opcode_decoded(opcode)?;
        } else if opc == 0b1000 {
            // 0 1 1 1 1 1 1 1 | 1 0 0 0 ...
            let opcode = [
                Opcode::SUNTIL_B, Opcode::SUNTIL_W, Opcode::SUNTIL_L, Opcode::SCMPU,
                Opcode::SWHILE_B, Opcode::SWHILE_W, Opcode::SWHILE_L, Opcode::SMOVU,
                Opcode::SSTR_B, Opcode::SSTR_W, Opcode::SSTR_L, Opcode::SMOVB,
                Opcode::RMPA_B, Opcode::RMPA_W, Opcode::RMPA_L, Opcode::SMOVF,
            ][operands as usize & 0b1111];
            handler.on_opcode_decoded(opcode)?;
        } else if opc == 0b1001 {
            // 0 1 1 1 1 1 1 1 | 1 0 0 1 ...
            let opcode = match operands & 0b1111 {
                0b0011 => Opcode::SATR,
                0b0100 => Opcode::RTFI,
                0b0101 => Opcode::RTE,
                0b0110 => Opcode::WAIT,
                _ => {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
            };
            handler.on_opcode_decoded(opcode)?;
        } else if opc == 0b1010 {
            // setpsw
            handler.on_operand_decoded(0, decoder.num_to_psw_bit(operands & 0b1111)?)?;
            handler.on_opcode_decoded(Opcode::SETPSW)?;
        } else if opc == 0b1011 {
            // clrpsw
            handler.on_operand_decoded(0, decoder.num_to_psw_bit(operands & 0b1111)?)?;
            handler.on_opcode_decoded(Opcode::CLRPSW)?;
        } else {
            return Err(StandardDecodeError::InvalidOpcode);
        }
    } else if opc < 0b1111_0000 {
        // 1 0 x x x x x x MOV
        // 1 1 x x <11 <11 MOV
        let sz = (opc >> 4) & 0b11;
        if sz == 0b11 {
            // definitely `1 0 1 1`: `1 1 1 1` would fail the branch above
            // disp[Rs], Rd
            handler.on_opcode_decoded(Opcode::MOVU)?;
            let sz = if (opc >> 3) & 0b1 != 0 {
                SizeCode::B
            } else {
                SizeCode::W
            };
            let operands = handler.read_u8(words)?;
            let rs = operands & 0b111;
            let rd = (operands >> 4) & 0b111;
            let displo = (operands >> 3) & 1;
            let dispmid = (operands >> 6) & 2;
            let disphi = (opc & 0b111) << 2;
            let disp = displo | dispmid | disphi;
            handler.on_operand_decoded(0, Operand::Deref { gpr: rs, disp: disp as u32, width: sz })?;
            handler.on_operand_decoded(1, Operand::Register { num: rd })?;
        } else {
            handler.on_opcode_decoded(Opcode::MOV)?;
            let sz = [SizeCode::B, SizeCode::W, SizeCode::L][sz as usize];
            // sz = 00, 01, 10, one of two styles of `mov`.
            if opc & 0b0100_0000 == 0 {
                // disp is 5-bit embedded form
                let operands = handler.read_u8(words)?;
                let rs = operands & 0b111;
                let rd = (operands >> 4) & 0b111;
                let displo = (operands >> 3) & 1;
                let dispmid = (operands >> 6) & 2;
                let disphi = (opc & 0b111) << 2;
                let disp = displo | dispmid | disphi;
                if opc & 0b0000_1000  == 0 {
                    handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                    handler.on_operand_decoded(1, Operand::Deref { gpr: rd, disp: disp as u32, width: sz })?;
                } else {
                    handler.on_operand_decoded(0, Operand::Deref { gpr: rs, disp: disp as u32, width: sz })?;
                    handler.on_operand_decoded(1, Operand::Register { num: rd })?;
                }
            } else {
                // either operand may have displacement, may be mem-mem
                let ldd = (opc >> 2) & 0b11;
                let lds = opc & 0b11;
                let operands = handler.read_u8(words)?;
                let rs = operands & 0b1111;
                let rd = operands >> 4;

                match (ldd, lds) {
                    (0b11, 0b11) => {
                        // encoding 7, explicitly reg-reg, might involve sign/zero extension
                        let source_op = if sz == SizeCode::L {
                            Operand::Register { num: rs }
                        } else {
                            Operand::Subreg { num: rs, width: sz }
                        };
                        handler.on_operand_decoded(0, source_op)?;
                        handler.on_operand_decoded(1, Operand::Register { num: rd })?;
                    }
                    (ld, 0b11) => {
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        let op = handler.decode_mem_op(rd, ld, sz, words)?;
                        handler.on_operand_decoded(1, op)?;
                    },
                    (0b11, ld) => {
                        // for this one, rs and rd are reversed...
                        let rs = operands >> 4;
                        let rd = operands & 0b1111;
                        let op = handler.decode_mem_op(rs, ld, sz, words)?;
                        handler.on_operand_decoded(0, op)?;
                        handler.on_operand_decoded(1, Operand::Register { num: rd })?;
                    },
                    (ldd, lds) => {
                        let op = handler.decode_mem_op(rs, lds, sz, words)?;
                        handler.on_operand_decoded(0, op)?;
                        let op = handler.decode_mem_op(rd, ldd, sz, words)?;
                        handler.on_operand_decoded(1, op)?;
                    }
                }
            }
        }
    } else if opc < 0b1111_0100 {
        // 1 1 1 1 0 0 x x BSET/BCLR
        let ld = opc & 0b11;
        if ld == 0b11 {
            return Err(StandardDecodeError::InvalidOperand);
        }

        let operands = handler.read_u8(words)?;
        let imm = operands & 0b111;
        let rd = operands >> 4;

        let operand = handler.decode_mem_op(rd, ld, SizeCode::B, words)?;

        let opcode = if operands & 0b0000_1000 == 0 {
            Opcode::BSET
        } else {
            Opcode::BCLR
        };
        handler.on_opcode_decoded(opcode)?;
        handler.on_operand_decoded(0, Operand::ImmB { imm })?;
        handler.on_operand_decoded(1, operand)?;
    } else if opc < 0b1111_1000 {
        // 1 1 1 1 0 1 x x BTST/PUSH
        let ld = opc & 0b11;
        if ld == 0b11 {
            return Err(StandardDecodeError::InvalidOperand);
        }

        let operands = handler.read_u8(words)?;
        let rs = operands >> 4;
        if operands & 0b0000_1000 == 0 {
            let imm = operands & 0b111;
            let op = handler.decode_mem_op(ld, rs, SizeCode::B, words)?;
            handler.on_operand_decoded(1, op)?;
            handler.on_operand_decoded(0, Operand::ImmB { imm })?;
            handler.on_opcode_decoded(Opcode::BTST)?;
        } else if operands & 0b0000_1100 == 0b0000_1000 {
            let sz = match operands & 0b11 {
                0b00 => SizeCode::B,
                0b01 => SizeCode::W,
                0b10 => SizeCode::L,
                _ => { unreachable!("checked for ld!=11 earlier"); }
            };

            let op = handler.decode_mem_op(ld, rs, sz, words)?;
            handler.on_operand_decoded(0, op)?;
            handler.on_opcode_decoded(Opcode::PUSH)?;
        } else {
            return Err(StandardDecodeError::InvalidOperand);
        }
    } else if opc < 0b1111_1100 {
        // 1 1 1 1 1 0 x x MOV (or v3+, DMOV)
        let ld = opc & 0b11;
        let operands = handler.read_u8(words)?;
        let sz = operands & 0b11;
        if sz == 0b11 {
            if decoder.version < RxVersion::V3 {
                // rxv1 or rxv2, no dmov yet, so this is an invalid `sz` for `mov`
                return Err(StandardDecodeError::InvalidOperand);
            } else {
                // rxv3+, dmov.*
                if operands != 0b0000_0011 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                let operands = handler.read_u8(words)?;
                let rd = operands >> 4;
                match operands & 0b1111 {
                    0b0000 => {
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(1, Operand::DoubleRegLow { num: rd })?;
                    },
                    0b0010 => {
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(1, Operand::DoubleRegHigh { num: rd })?;
                    },
                    0b0011 => {
                        // not really sure what makes the immediate D size here. does hardware
                        // expand the 32b float into a 64b float?
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
                    },
                    _ => {
                        return Err(StandardDecodeError::InvalidOpcode);
                    }
                }
                let imm = handler.read_u32(words)?;
                handler.on_operand_decoded(0, Operand::ImmL { imm })?;
            }
        } else {
            let rd = operands >> 4;
            let li = (operands >> 2) & 0b11;
            let sz = [SizeCode::B, SizeCode::W, SizeCode::L][sz as usize];
            // note this is a bit of a lie: `li=10` is actually a 24b immediate, but for comparison
            // here L is close enough..
            let li_code = [SizeCode::B, SizeCode::W, SizeCode::L, SizeCode::L][li as usize];
            // what happens when `li` is larger than `sz`...??? undefined!
            if li_code.bytes() > sz.bytes() {
                return Err(StandardDecodeError::InvalidOperand);
            }

            let operand = handler.decode_mem_op(ld, rd, sz, words)?;
            let imm = match li {
                0b00 => {
                    handler.read_u32(words)?
                }
                0b01 => {
                    handler.read_u8(words)? as i8 as i32 as u32
                }
                0b10 => {
                    handler.read_u16(words)? as i16 as i32 as u32
                }
                _ => {
                    debug_assert!(li == 0b11, "li is at most the low two bits set");
                    handler.read_i24(words)? as u32
                }
            };
            handler.on_opcode_decoded(Opcode::MOV)?;
            handler.on_operand_decoded(0, Operand::ImmL { imm })?;
            handler.on_operand_decoded(1, operand)?;
        }
    } else if opc == 0b1111_1100 {
        // many instructions
        let operands = handler.read_u8(words)?;
        let opc5 = (operands >> 2) & 0b11111;
        let ld = operands & 0b11;

        let registers = handler.read_u8(words)?;
        let rd = registers & 0b1111;
        let rs = registers >> 4;

        if operands & 0b1000_0000 == 0 {
            // 1 1 1 1 1 1 0 0 | 0 ..
            if opc5 < 0b10010 {
                // simple enough: `0 [ opc5 ] ld | [ rs  ] [ rd  ]`
                let opcode = match opc5 {
                    0b00000 => {
                        if ld != 0b11 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        Opcode::SBB
                    }
                    0b00001 => {
                        if ld != 0b11 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        Opcode::NEG
                    }
                    0b00010 => {
                        if ld != 0b11 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        Opcode::ADC
                    }
                    0b00011 => {
                        if ld != 0b11 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        Opcode::ABS
                    }
                    0b00100 => Opcode::MAX,
                    0b00101 => Opcode::MIN,
                    0b00110 => Opcode::EMUL,
                    0b00111 => Opcode::EMULU,
                    0b01000 => Opcode::DIV,
                    0b01001 => Opcode::DIVU,
                    0b01010 => { return Err(StandardDecodeError::InvalidOperand); },
                    0b01011 => { return Err(StandardDecodeError::InvalidOperand); },
                    0b01100 => Opcode::TST,
                    0b01101 => Opcode::XOR,
                    0b01110 => {
                        if ld != 0b11 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        Opcode::NOT
                    }
                    0b01111 => { return Err(StandardDecodeError::InvalidOperand); },
                    0b10000 => Opcode::XCHG,
                    _ => {
                        debug_assert!(opc5 == 0b10001, "checked opc is below 0b10010");
                        Opcode::ITOF
                    }
                };
                handler.on_opcode_decoded(opcode)?;
                let source = handler.decode_mem_op(ld, rs, SizeCode::L, words)?;
                handler.on_operand_decoded(0, source)?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            } else if opc5 < 0b10100 {
                // opc is larger. decoding gets more custom..
                if decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                handler.on_opcode_decoded(if opc5 & 1 == 0 {
                    Opcode::STZ
                } else {
                    Opcode::STNZ
                })?;
                handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            } else if opc5 < 0b10101 {
                // 1 1 1 1 1 1 0 0 | 0 1 0 1 0 0 ..
                // nothing here (yet?)
                return Err(StandardDecodeError::InvalidOpcode);
            } else if opc5 < 0b10110 {
                // 1 1 1 1 1 1 0 0 | 0 1 0 1 0 1 ..
                // utof
                if decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                handler.on_opcode_decoded(Opcode::UTOF)?;
                let op = handler.decode_mem_op(ld, rs, SizeCode::L, words)?;
                handler.on_operand_decoded(0, op)?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            } else if opc5 < 0b11000 {
                // 1 1 1 1 1 1 0 0 | 0 1 1 0 x x ..
                // bfmov{,z}
                if decoder.version < RxVersion::V3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                let regs = handler.read_u8(words)?;
                handler.on_opcode_decoded(if opc5 & 1 == 0 {
                    Opcode::BFMOVZ
                } else {
                    Opcode::BFMOV
                })?;
                let rs = regs >> 4;
                let rd = regs & 0b1111;

                let bits = handler.read_u16(words)?;
                handler.on_operand_decoded(0, Operand::BitfieldSpec { bf_spec: BitfieldSpec { bits } })?;
                handler.on_operand_decoded(1, Operand::Register { num: rs })?;
                handler.on_operand_decoded(2, Operand::Register { num: rd })?;
            } else if opc5 < 0b11100 {
                let opcode = [Opcode::BSET, Opcode::BCLR, Opcode::BTST, Opcode::BNOT][opc5 as usize & 0b11];
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                let op = handler.decode_mem_op(ld, rd, SizeCode::B, words)?;
                handler.on_operand_decoded(1, op)?;
            } else if opc5 == 0b11110 {
                if decoder.version < RxVersion::V3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                let regs = handler.read_u8(words)?;
                let regs_lo = regs & 0b1111;
                // this encoding of dmov.d just.. requires 1000 here? no reason as far as i can
                // see, it Just Does.
                if regs_lo != 0b1000 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                let rd = regs >> 4;
                let dest_op = handler.decode_mem_op(ld, rd, SizeCode::D, words)?;
                let regs = handler.read_u8(words)?;
                let rs = regs >> 4;
                let regs_lo = regs & 0b1111;
                // similarly, just requires that the low four bits here are all 0.
                if regs_lo != 0b0000 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                handler.on_opcode_decoded(Opcode::DMOV)?;
                handler.on_operand_decoded(0, Operand::DoubleReg { num: rs })?;
                handler.on_operand_decoded(1, dest_op)?;
            } else {
                // 1 1 1 1 1 1 0 0 | 0 1 1 1 1 l ...
                return Err(StandardDecodeError::InvalidOpcode);
            }
        } else {
            // 1 1 1 1 1 1 0 0 | 1 ..
            if opc5 < 0b10000 {
                let opcode = match opc5 & 0b1111 {
                    0b0000 => Opcode::FSUB,
                    0b0001 => Opcode::FCMP,
                    0b0010 => Opcode::FADD,
                    0b0011 => Opcode::FMUL,
                    0b0100 => Opcode::FDIV,
                    0b0101 => Opcode::FTOI,
                    0b0110 => Opcode::ROUND,
                    0b1000 => {
                        if decoder.version < RxVersion::V2 {
                            return Err(StandardDecodeError::InvalidOpcode);
                        }
                        Opcode::FSQRT
                    },
                    0b1001 => {
                        if decoder.version < RxVersion::V2 {
                            return Err(StandardDecodeError::InvalidOpcode);
                        }
                        Opcode::FTOU
                    },
                    _ => {
                        return Err(StandardDecodeError::InvalidOpcode);
                    }
                };
                let regs = handler.read_u8(words)?;
                let rs = regs >> 4;
                let rd = regs & 0b1111;
                let source = handler.decode_mem_op(ld, rs, SizeCode::D, words)?;
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, source)?;
                handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
            } else if opc5 == 0b10010 {
                // 1 1 1 1 1 1 0 0 | 1 1 0 0 1 0 ..
                // dmovd
                if decoder.version < RxVersion::V3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                let operands = handler.read_u8(words)?;
                let rs = operands >> 4;
                if operands & 0b1111 != 0b1000 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                let source = handler.decode_mem_op(ld, rs, SizeCode::D, words)?;
                let operands = handler.read_u8(words)?;
                let rd = operands >> 4;
                if operands & 0b1111 != 0b0000 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                handler.on_opcode_decoded(Opcode::DMOV)?;
                handler.on_operand_decoded(0, source)?;
                handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
            } else if opc5 < 0b11000 {
                // 1 1 1 1 1 1 0 0 | 1 1 0 1 sz ..
                // SCCnd.size
                let operands = handler.read_u8(words)?;
                let rd = operands >> 4;
                let cnd = operands & 0b1111;
                let sz = match opc5 & 0b11 {
                    0b00 => SizeCode::B,
                    0b01 => SizeCode::W,
                    0b10 => SizeCode::L,
                    _ => {
                        return Err(StandardDecodeError::InvalidOperand);
                    }
                };
                if cnd >= 0b1110 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                let opcode = [
                    Opcode::SCEQ, Opcode::SCNE, Opcode::SCGEU, Opcode::SCLTU,
                    Opcode::SCGTU, Opcode::SCLEU, Opcode::SCPZ, Opcode::SCN,
                    Opcode::SCGE, Opcode::SCLT, Opcode::SCGT, Opcode::SCLE,
                    Opcode::SCO, Opcode::SCNO, Opcode::NOP, Opcode::NOP // "NOP" is never reached: cnd>=1110, invalid above
                ][cnd as usize];
                handler.on_opcode_decoded(opcode)?;
                let op = handler.decode_mem_op(ld, rd, sz, words)?;
                handler.on_operand_decoded(0, op)?;
            } else if opc5 >= 0b11000 {
                // 1 1 1 1 1 1 0 0 | 1 1 1 [imm3] ..
                let operands = handler.read_u8(words)?;
                let rd = operands >> 4;
                let cnd = operands & 0b1111;
                let imm = opc5 & 0b111;

                if ld == 0b11 {
                    return Err(StandardDecodeError::InvalidOperand);
                }

                let opcode = if cnd == 0b1111 {
                    Opcode::BNOT
                } else if cnd == 0b1110 {
                    return Err(StandardDecodeError::InvalidOpcode);
                } else {
                    [
                        Opcode::BMEQ, Opcode::BMNE, Opcode::BMGEU, Opcode::BMLTU,
                        Opcode::BMGTU, Opcode::BMLEU, Opcode::BMPZ, Opcode::BMN,
                        Opcode::BMGE, Opcode::BMLT, Opcode::BMGT, Opcode::BMLE,
                        Opcode::BMO, Opcode::BMNO, Opcode::NOP, Opcode::NOP // "NOP" is never reached: cnd>=1110, invalid above
                    ][cnd as usize]
                };
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::ImmB { imm })?;
                let op = handler.decode_mem_op(ld, rd, SizeCode::B, words)?;
                handler.on_operand_decoded(1, op)?;
            } else {
                unreachable!("should be unreachable, fuzzing will tell..");
            }
        }
    } else if opc == 0b1111_1101 {
        // many instructions
        // for *almost* everything under this category, the next byte also picks opcodes. some use
        // bits here for operands though.
        let opcode = handler.read_u8(words)?;

        if opcode < 0b1000_0000 {
            // 1 1 1 1 1 1 0 1 | 0 ....
            if opcode < 0b0001_0000 {
                let a = (opcode >> 3) & 1;
                if a != 0 && decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOperand);
                }

                let regs = handler.read_u8(words)?;
                let rs = regs >> 4;
                let rs2 = regs & 0b1111;

                // hokey, but this does filter for mullh, emula, maclh, and emaca
                if opcode & 0b010 != 0b000 && decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                let opcode = match opcode & 0b111 {
                    0b000 => Opcode::MULHI,
                    0b001 => Opcode::MULLO,
                    0b010 => Opcode::MULLH,
                    0b011 => Opcode::EMULA,
                    0b100 => Opcode::MACHI,
                    0b101 => Opcode::MACLO,
                    0b110 => Opcode::MACLH,
                    _ => Opcode::EMACA,
                };
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                handler.on_operand_decoded(1, Operand::Register { num: rs2 })?;
                handler.on_operand_decoded(2, Operand::Accumulator { num: a })?;
            } else if opcode == 0b0001_0111 {
                let operands = handler.read_u8(words)?;
                let rs = operands & 0b1111;
                let opc = (operands >> 4) & 0b111;
                let a = operands >> 7;

                if a != 0 && decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOperand);
                }

                let opcode = match opc {
                    0b000 => Opcode::MVTACHI,
                    0b001 => Opcode::MVTACLO,
                    0b011 => {
                        if decoder.version < RxVersion::V2 {
                            return Err(StandardDecodeError::InvalidOpcode);
                        }
                        Opcode::MVTACGU
                    }
                    _ => {
                        return Err(StandardDecodeError::InvalidOpcode);
                    }
                };
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                handler.on_operand_decoded(1, Operand::Accumulator { num: a })?;
            } else if opcode & 0b1111_1110 == 0b0001_1000 {
                // we can use the lowest bit of opcode to decide if this is racw/racl (0==racw)
                let wide = opcode & 1;

                let operands = handler.read_u8(words)?;
                if operands & 0b1111 != 0 {
                    return Err(StandardDecodeError::InvalidOperand);
                }
                let imm = (operands >> 4) & 0b11;
                let opc = (operands >> 6) & 1;
                let a = operands >> 7;

                if imm > 0b01 {
                    return Err(StandardDecodeError::InvalidOperand);
                }

                if a != 0 && decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOperand);
                }

                let opcode = if opc == 0 {
                    if wide == 0 { Opcode::RACW } else { Opcode::RACL }
                } else if decoder.version >= RxVersion::V2 {
                    if wide == 0 { Opcode::RDACW } else { Opcode::RDACL }
                } else {
                    return Err(StandardDecodeError::InvalidOpcode);
                };
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::ImmB { imm: imm + 1 })?;
                handler.on_operand_decoded(1, Operand::Accumulator { num: a })?;
            } else if opcode & 0b1111_1110 == 0b0001_1110 {
                let operands = handler.read_u8(words)?;
                let rd = operands & 0b1111;
                let immlo = (operands >> 6) & 1;
                let immhi = opcode & 1;
                let imm = (immhi << 1) | immlo;
                let opc = (operands >> 4) & 0b11;
                let a = operands >> 7;

                let opcode = match opc {
                    0b00 => Opcode::MVFACHI,
                    0b01 => {
                        if decoder.version < RxVersion::V2 {
                            return Err(StandardDecodeError::InvalidOpcode);
                        }
                        Opcode::MVFACLO
                    }
                    0b10 => Opcode::MVFACMI,
                    _ => {
                        if decoder.version < RxVersion::V2 {
                            return Err(StandardDecodeError::InvalidOpcode);
                        }
                        Opcode::MVFACGU
                    }
                };

                if imm != 0 && decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOperand);
                }

                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::ImmB { imm })?;
                handler.on_operand_decoded(1, Operand::Accumulator { num: a })?;
                handler.on_operand_decoded(2, Operand::Register { num: rd })?;
            } else if opcode < 0b0100_0000 {
                // 1 1 1 1 1 1 0 1 | 0 0 1 x x x x x
                // nothing here yet
                return Err(StandardDecodeError::InvalidOpcode);
            } else if opcode < 0b0101_0000 {
                // 1 1 1 1 1 1 0 1 | 0 1 0 0 a x x x
                if opcode & 0b0000_0100 != 0 {
                    // nothing here, msbhi and friends require bit above xx to be 1
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                if decoder.version < RxVersion::V2 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                let a = (opcode >> 3) & 1;
                let opc = opcode & 0b11;
                let operands = handler.read_u8(words)?;
                let rs = operands >> 4;
                let rs2 = operands & 0b1111;

                let opcode = [Opcode::MSBHI, Opcode::MSBLH, Opcode::MSBLO, Opcode::EMSBA][opc as usize];
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                handler.on_operand_decoded(1, Operand::Register { num: rs2 })?;
                handler.on_operand_decoded(2, Operand::Accumulator { num: a })?;
            } else if opcode < 0b0110_0000 {
                // 1 1 1 1 1 1 0 1 | 0 1 0 1 x x x x
                // nothing here yet either
                return Err(StandardDecodeError::InvalidOpcode);
            } else if opcode < 0b0110_1000 {
                // 1 1 1 1 1 1 0 1 | 0 1 1 0 0 x x x
                let operands = handler.read_u8(words)?;
                let rd = operands & 0b1111;
                let rs = operands >> 4;

                let opcode = match opcode & 0b111 {
                    0b000 => Opcode::SHLR,
                    0b001 => Opcode::SHAR,
                    0b010 => Opcode::SHLL,
                    0b011 => { return Err(StandardDecodeError::InvalidOpcode); },
                    0b100 => Opcode::ROTR,
                    0b101 => Opcode::REVW,
                    0b110 => Opcode::ROTL,
                    _ => Opcode::REVL,
                };

                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            } else if opcode == 0b0110_1000 {
                let operands = handler.read_u8(words)?;
                let cr = operands & 0b1111;
                let rs = operands >> 4;

                if cr == 0b0010 {
                    // can't move to pc
                    return Err(StandardDecodeError::InvalidOperand);
                }
                handler.on_opcode_decoded(Opcode::MVTC)?;
                handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                handler.on_operand_decoded(1, decoder.reg_to_control_reg(cr)?)?;
            } else if opcode == 0b0110_1010 {
                let operands = handler.read_u8(words)?;
                let rd = operands & 0b1111;
                let cr = operands >> 4;

                handler.on_opcode_decoded(Opcode::MVFC)?;
                handler.on_operand_decoded(0, decoder.reg_to_control_reg(cr)?)?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            } else if opcode < 0b0110_1100 {
                return Err(StandardDecodeError::InvalidOpcode);
            } else if opcode < 0b0111_0000 {
                // 1 1 1 1 1 1 0 1 | 0 1 1 0 1 1 x x
                // rotr/rotl
                let operands = handler.read_u8(words)?;
                let rd = operands & 0b1111;
                let immlo = operands >> 4;
                let immhi = opcode & 1;
                let imm = (immhi << 4) | immlo;
                handler.on_opcode_decoded(if opcode & 0b10 == 0 {
                    Opcode::ROTR
                } else {
                    Opcode::ROTL
                })?;
                handler.on_operand_decoded(0, Operand::ImmB { imm })?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            } else if opcode == 0b0111_0101 {
                if decoder.version < RxVersion::V3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                let operands = handler.read_u8(words)?;
                if operands & 0b1111_0000 != 0b1000_0000 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                let rd = operands & 0b1111;
                let operands = handler.read_u8(words)?;
                let opc = operands & 0b1111;
                let rs = operands >> 4;

                match opc {
                    0b0000 => {
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(0, Operand::DoubleRegLow { num: rs })?;
                        handler.on_operand_decoded(1, Operand::Register { num: rd })?;
                    }
                    0b0010 => {
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(0, Operand::DoubleRegHigh { num: rs })?;
                        handler.on_operand_decoded(1, Operand::Register { num: rd })?;
                    }
                    0b0100 => {
                        handler.on_opcode_decoded(Opcode::MVFDC)?;
                        handler.on_operand_decoded(0, Operand::DoubleRegHigh { num: rs })?;
                        handler.on_operand_decoded(1, decoder.reg_to_double_control_reg(rd)?)?;
                    }
                    _ => { return Err(StandardDecodeError::InvalidOpcode) }
                }
            } else if opcode == 0b0111_0110 {
                if decoder.version < RxVersion::V3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                let operands = handler.read_u8(words)?;
                let opc = operands >> 4;
                let rs = operands & 0b1111;
                let imm = handler.read_u8(words)?;

                match opc {
                    0b1100 => {
                        if imm != 0b0000_0000 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        handler.on_opcode_decoded(Opcode::SAVE)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                    }
                    0b1101 => {
                        if imm != 0b0000_0000 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        handler.on_opcode_decoded(Opcode::RSTR)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                    }
                    0b1110 => {
                        if rs != 0b0000_0000 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        handler.on_opcode_decoded(Opcode::SAVE)?;
                        handler.on_operand_decoded(0, Operand::ImmB { imm })?;
                    }
                    0b1111 => {
                        if rs != 0b0000_0000 {
                            return Err(StandardDecodeError::InvalidOperand);
                        }
                        handler.on_opcode_decoded(Opcode::RSTR)?;
                        handler.on_operand_decoded(0, Operand::ImmB { imm })?;
                    }
                    _ => { return Err(StandardDecodeError::InvalidOpcode) }
                };
            } else if opcode == 0b0111_0111 {
                if decoder.version < RxVersion::V3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }

                let operands = handler.read_u8(words)?;
                if operands & 0b1111_0000 != 0b1000_0000 {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
                let rs = operands & 0b1111;
                let operands = handler.read_u8(words)?;
                let rd = operands >> 4;
                let opc = operands & 0b1111;
                match opc {
                    0b0000 => {
                        // dmov.l from gpr to drlN (encoding 3)
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        handler.on_operand_decoded(1, Operand::DoubleRegLow { num: rd })?;
                    }
                    0b0010 => {
                        // dmov.l from gpr to drhN (encoding 2)
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        handler.on_operand_decoded(1, Operand::DoubleRegHigh { num: rd })?;
                    }
                    0b0011 => {
                        // mov.d from gpr to drhN (encoding 1) (... ? what ... )
                        handler.on_opcode_decoded(Opcode::DMOV)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
                    }
                    0b0100 => {
                        // mvtdc
                        let cr = decoder.reg_to_double_control_reg(rd)?;
                        handler.on_opcode_decoded(Opcode::MVTDC)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        handler.on_operand_decoded(1, cr)?;
                    }
                    0b1001 => {
                        // itod
                        handler.on_opcode_decoded(Opcode::ITOD)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
                    }
                    0b1010 => {
                        // ftod
                        handler.on_opcode_decoded(Opcode::FTOD)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
                    }
                    0b1101 => {
                        // utod
                        handler.on_opcode_decoded(Opcode::UTOD)?;
                        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
                        handler.on_operand_decoded(1, Operand::DoubleReg { num: rd })?;
                    }
                    _ => {
                        return Err(StandardDecodeError::InvalidOpcode);
                    }
                }
            } else if opcode < 0b0111_0000 {
                // any unhandled cases below 0111_0000, which need more... careful handling.
                return Err(StandardDecodeError::InvalidOpcode);
            } else {
                let li = (opcode >> 2) & 0b11;
                let opc_lo = opcode & 0b11;
                if opc_lo == 0b00 {
                    // 1 1 1 1 1 1 0 1 | 0 1 1 1 xx  0 0 | ...
                    // <op> imm, reg
                    let opcode = handler.read_u8(words)?;
                    let rd = opcode & 0b1111;
                    let opcode = opcode >> 4;
                    let opcode = match opcode {
                        0b0010 => Opcode::ADC,
                        0b0100 => Opcode::MAX,
                        0b0101 => Opcode::MIN,
                        0b0110 => Opcode::EMUL,
                        0b0111 => Opcode::EMULU,
                        0b1000 => Opcode::DIV,
                        0b1001 => Opcode::DIVU,
                        0b1100 => Opcode::TST,
                        0b1101 => Opcode::XOR,
                        0b1110 => Opcode::STZ,
                        0b1111 => Opcode::STNZ,
                        _ => { return Err(StandardDecodeError::InvalidOpcode) }
                    };
                    handler.on_opcode_decoded(opcode)?;
                    let imm = match li {
                        0b00 => {
                            handler.read_u32(words)?
                        }
                        0b01 => {
                            handler.read_u8(words)? as i8 as i32 as u32
                        }
                        0b10 => {
                            handler.read_u16(words)? as i16 as i32 as u32
                        }
                        _ => {
                            debug_assert!(li == 0b11, "li is at most the low two bits set");
                            handler.read_i24(words)? as u32
                        }
                    };
                    handler.on_operand_decoded(0, Operand::ImmL { imm })?;
                    handler.on_operand_decoded(1, Operand::Register { num: rd })?;
                } else if opc_lo == 0b11 {
                    // 1 1 1 1 1 1 0 1 | 0 1 1 1 xx  1 1 | ...
                    // mvtc imm, creg
                    let opcode = handler.read_u8(words)?;
                    let rd = opcode & 0b1111;
                    let opcode = opcode >> 4;
                    if opcode != 0b0000 {
                        return Err(StandardDecodeError::InvalidOpcode);
                    }
                    if rd == 0b0001 {
                        // can't set pc
                        return Err(StandardDecodeError::InvalidOperand);
                    }
                    let cr = decoder.reg_to_control_reg(rd)?;
                    handler.on_opcode_decoded(Opcode::MVTC)?;
                    let imm = match li {
                        0b00 => {
                            handler.read_u32(words)?
                        }
                        0b01 => {
                            handler.read_u8(words)? as i8 as i32 as u32
                        }
                        0b10 => {
                            handler.read_u16(words)? as i16 as i32 as u32
                        }
                        _ => {
                            debug_assert!(li == 0b11, "li is at most the low two bits set");
                            handler.read_i24(words)? as u32
                        }
                    };
                    handler.on_operand_decoded(0, Operand::ImmL { imm })?;
                    handler.on_operand_decoded(1, cr)?;
                } else if opc_lo == 0b10 {
                    // 1 1 1 1 1 1 0 1 | 0 1 1 1 xx  1 0 | ...
                    // <float op> imm, reg
                    if li != 0b00 {
                        return Err(StandardDecodeError::InvalidOperand);
                    }

                    let opcode = handler.read_u8(words)?;
                    let rd = opcode & 0b1111;
                    let opcode = opcode >> 4;
                    if opcode > 0b100 {
                        return Err(StandardDecodeError::InvalidOpcode);
                    }
                    handler.on_opcode_decoded(
                        [Opcode::FSUB, Opcode::FCMP, Opcode::FADD, Opcode::FMUL, Opcode::FDIV][opcode as usize]
                    )?;
                    let imm = handler.read_u32(words)?;
                    handler.on_operand_decoded(0, Operand::ImmL { imm })?;
                    handler.on_operand_decoded(1, Operand::Register { num: rd })?;
                } else {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
            }
        } else {
            // 1 1 1 1 1 1 0 1 | 1 ....
            // TODO:
            let opc = (opcode >> 5) & 0b11;
            let imm5 = opcode & 0b1_1111;

            let operands = handler.read_u8(words)?;
            let rd = operands & 0b1111;
            let rs2 = operands >> 4;

            if opc == 0b11 {
                // bmcnd/bnot
                let cnd = rs2;
                let opcode = [
                    Opcode::BMEQ, Opcode::BMNE, Opcode::BMGEU, Opcode::BMLTU,
                    Opcode::BMGTU, Opcode::BMLEU, Opcode::BMPZ, Opcode::BMN,
                    Opcode::BMGE, Opcode::BMLT, Opcode::BMGT, Opcode::BMLE,
                    Opcode::BMO, Opcode::BMNO, Opcode::NOP, Opcode::BNOT // "NOP" is never reached: cnd>=1110, invalid above
                ][cnd as usize];
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::ImmB { imm: imm5 })?;
                handler.on_operand_decoded(1, Operand::Register { num: rd })?;
            } else {
                let opcode = [Opcode::SHLR, Opcode::SHAR, Opcode::SHLL][opc as usize];
                handler.on_opcode_decoded(opcode)?;
                handler.on_operand_decoded(0, Operand::ImmB { imm: imm5 })?;
                handler.on_operand_decoded(1, Operand::Register { num: rs2 })?;
                handler.on_operand_decoded(2, Operand::Register { num: rd })?;
            }
        }
    } else if opc == 0b1111_1110 {
        // mov
        let operands = handler.read_u8(words)?;
        let next_regs = handler.read_u8(words)?;
        let ri = operands & 0b1111;
        let rb = next_regs >> 4;
        let rd = next_regs & 0b1111;
        let sz = (operands >> 4) & 0b11;

        if sz == 0b11 {
            return Err(StandardDecodeError::InvalidOperand);
        }

        let sz = [SizeCode::B, SizeCode::W, SizeCode::L][sz as usize];

        if operands < 0b0100_0000 {
            handler.on_opcode_decoded(Opcode::MOV)?;
            handler.on_operand_decoded(0, Operand::Register { num: rd })?;
            handler.on_operand_decoded(1, Operand::DerefIndexed { base: rb, index: ri, width: sz })?;
        } else if operands < 0b1000_0000 {
            handler.on_opcode_decoded(Opcode::MOV)?;
            handler.on_operand_decoded(0, Operand::DerefIndexed { base: rb, index: ri, width: sz })?;
            handler.on_operand_decoded(1, Operand::Register { num: rd })?;
        } else if operands < 0b1100_0000 {
            // 1 1 1 1 1 1 1 0 | 1 0 ..
            // nothing encoded here
            return Err(StandardDecodeError::InvalidOpcode);
        } else if operands < 0b1110_0000 {
            if sz == SizeCode::L {
                return Err(StandardDecodeError::InvalidOperand);
            }

            handler.on_opcode_decoded(Opcode::MOVU)?;
            handler.on_operand_decoded(0, Operand::DerefIndexed { base: rb, index: ri, width: sz })?;
            handler.on_operand_decoded(1, Operand::Register { num: rd })?;
        } else {
            return Err(StandardDecodeError::InvalidOpcode);
        }
    } else if opc == 0b1111_1111 {
        // 3-operand instructions
        let operands = handler.read_u8(words)?;
        let rd = operands & 0b1111;
        let opc = operands >> 4;
        let extra_regs = handler.read_u8(words)?;
        let rs2 = extra_regs & 0b1111;
        let rs = extra_regs >> 4;

        let opc = match opc {
            0b0000 => Opcode::SUB,
            0b0010 => Opcode::ADD,
            0b0011 => Opcode::MUL,
            0b0100 => Opcode::AND,
            0b0101 => Opcode::OR,
            0b0110 => {
                if decoder.version >= RxVersion::V3 {
                    Opcode::XOR
                } else {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
            },
            0b1000 => {
                if decoder.version >= RxVersion::V2 {
                    Opcode::FSUB
                } else {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
            },
            0b1010 => {
                if decoder.version >= RxVersion::V2 {
                    Opcode::FADD
                } else {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
            },
            0b1011 => {
                if decoder.version >= RxVersion::V2 {
                    Opcode::FMUL
                } else {
                    return Err(StandardDecodeError::InvalidOpcode);
                }
            },
            _ => {
                return Err(StandardDecodeError::InvalidOpcode);
            }
        };

        handler.on_opcode_decoded(opc)?;
        handler.on_operand_decoded(0, Operand::Register { num: rs })?;
        handler.on_operand_decoded(1, Operand::Register { num: rs2 })?;
        handler.on_operand_decoded(2, Operand::Register { num: rd })?;
    } else {
        unreachable!("fuzzing should show this to be unreachable");
    }

    Ok(())
}
