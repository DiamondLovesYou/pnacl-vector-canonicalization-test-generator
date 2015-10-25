
#![feature(zero_one)]

use std::cell::{RefCell, Cell};
use std::fs::{OpenOptions};
use std::io::{Write, Cursor};
use std::rc::Rc;

extern crate rand;

pub struct InstName {
    val: Cell<usize>,
}
impl InstName {
    fn new() -> InstName {
        return InstName { val: Cell::new(0) };
    }
    fn last(&self) -> usize { return self.val.get() - 1; }
    fn get(&self) -> usize {
        let c = self.val.get();
        self.val.set(c + 1);
        return c;
    }
    fn reset(&self) { self.reset_to(0); }
    fn reset_to(&self, to: usize) {
        self.val.set(to);
    }
}

#[derive(Copy, Clone)]
enum ImplMethod {
    Scalar,
    Vector,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum LLVMType {
    I1,
    I8, I16, I32, I64,
    I8Ptr,
    F32, F64,
}

impl LLVMType {
    pub fn llvm_type_str(&self) -> &'static str {
        match self {
            &LLVMType::I1 => "i1",
            &LLVMType::I8 => "i8",
            &LLVMType::I16 => "i16",
            &LLVMType::I32 => "i32",
            &LLVMType::I64 => "i64",
            &LLVMType::I8Ptr => "i8*",
            &LLVMType::F32 => "float",
            &LLVMType::F64 => "double",
        }
    }
    pub fn legal_name(&self) -> String {
        let llvm_type = self.llvm_type_str();
        if llvm_type.ends_with('*') {
            format!("{}ptr", &llvm_type[..llvm_type.len() - 1])
        } else {
            llvm_type.to_string()
        }
    }
    fn size(&self) -> usize {
        match self {
            &LLVMType::I1 => unreachable!(),
            &LLVMType::I8 => 1,
            &LLVMType::I16 => 2,
            &LLVMType::I32 => 4,
            &LLVMType::I64 => 8,
            &LLVMType::I8Ptr => 4,
            &LLVMType::F32 => 4,
            &LLVMType::F64 => 8,
        }
    }
    pub fn per_legal_vty(&self) -> usize { 16 / self.size() }

    pub fn is_intty(&self) -> bool {
        !self.is_fpty()
    }
    pub fn is_fpty(&self) -> bool {
        match self {
            &LLVMType::F32 | &LLVMType::F64 => true,
            _ => false,
        }
    }
}
impl Into<Ty> for LLVMType {
    fn into(self) -> Ty {
        Ty::Scalar(self)
    }
}
#[allow(non_upper_case_globals)] pub const I1Ty: LLVMType = LLVMType::I1;
#[allow(non_upper_case_globals)] pub const I8Ty: LLVMType = LLVMType::I8;
#[allow(non_upper_case_globals)] pub const I16Ty: LLVMType = LLVMType::I16;
#[allow(non_upper_case_globals)] pub const I32Ty: LLVMType = LLVMType::I32;
#[allow(non_upper_case_globals)] pub const I64Ty: LLVMType = LLVMType::I64;
#[allow(non_upper_case_globals)] pub const I8PtrTy: LLVMType = LLVMType::I8Ptr;
#[allow(non_upper_case_globals)] pub const F32Ty: LLVMType = LLVMType::F32;
#[allow(non_upper_case_globals)] pub const F64Ty: LLVMType = LLVMType::F64;

const SCALAR_TYPES: [LLVMType; 7] = [I8Ty, I16Ty, I32Ty, I64Ty, I8PtrTy, F32Ty, F64Ty];

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct VectorType {
    pub count: usize,
    pub inner: LLVMType,
}
impl VectorType {
    pub fn new(count: usize, inner: LLVMType) -> VectorType {
        VectorType {
            count: count,
            inner: inner
        }
    }
    pub fn count(&self) -> usize { self.count }
    pub fn split_part(&self, idx: usize) -> usize {
        use std::cmp::min;
        let parts = self.extra_parts();
        let part = idx * self.inner.size() / 16;
        min(parts, part)
    }
    pub fn split_parts(&self) -> usize {
        (self.count - 1) / self.inner.per_legal_vty() + 1
    }
    pub fn extra_parts(&self) -> usize {
        self.split_parts() - 1
    }
    pub fn part_index(&self, idx: usize) -> usize {
        idx - self.split_part(idx) * self.inner.per_legal_vty()
    }

    pub fn legalized_type(&self) -> (usize, VectorType) {
        let ty = VectorType {
            count: self.inner.per_legal_vty(),
            inner: self.inner,
        };
        (self.split_parts(), ty)
    }
    pub fn legal_type(&self) -> VectorType {
        VectorType {
            count: self.inner.per_legal_vty(),
            inner: self.inner,
        }
    }

    pub fn legal_name(&self) -> String {
        format!("{}x{}", self.count, self.inner.legal_name())
    }
    pub fn llvm_type_str(&self) -> String {
        format!("<{} x {}>", self.count, self.inner.llvm_type_str())
    }

    pub fn rem_last_split(&self) -> usize {
        if self.count() % self.inner.per_legal_vty() == 0 {
            0
        } else {
            self.count() - self.extra_parts() * self.inner.per_legal_vty()
        }
    }

    pub fn cmp_result(&self) -> VectorType {
        VectorType::new(self.count, I1Ty)
    }

    pub fn to_generic_ty(self) -> Ty {
        self.into()
    }
}
impl Into<Ty> for VectorType {
    fn into(self) -> Ty {
        Ty::Vector(self)
    }
}

macro_rules! vector_type(
    ($count:expr, $ty:expr) => {
        VectorType::new($count, $ty)
    }
);

pub type ScalarType = LLVMType;
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct ArrayType {
    pub count: u32,
    pub elem: Ty,
}
impl ArrayType {
    pub fn count(&self) -> u32 { self.count }
    pub fn llvm_type_str(&self) -> String {
        format!("[{} x {}]", self.count, self.elem.llvm_type_str())
    }
}
impl Into<Ty> for ArrayType {
    fn into(self) -> Ty {
        Ty::Array(Rc::new(self))
    }
}
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct FunctionType {
    pub ret: Option<Ty>,
    pub args: Vec<Ty>,
}
impl Default for FunctionType {
    fn default() -> FunctionType {
        FunctionType {
            ret: None,
            args: Vec::new(),
        }
    }
}
impl Into<Ty> for FunctionType {
    fn into(self) -> Ty {
        Ty::Function(Rc::new(self))
    }
}
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Ty {
    Void,
    Scalar(ScalarType),
    Vector(VectorType),
    Array(Rc<ArrayType>),

    /// NO RECURSION, at least for now.
    Struct {
        id: u32,
        elements: Vec<Rc<Ty>>,
    },

    Pointer(Rc<Ty>),
    Function(Rc<FunctionType>),
}
impl Ty {
    pub fn byte_size(&self) -> usize {
        match self {
            &Ty::Void => panic!("found zero-sized type"),
            &Ty::Scalar(inner) => inner.size(),
            &Ty::Vector(vty) => vty.count() * vty.inner.size(),
            &Ty::Array(ref aty) => {
                aty.count() as usize * aty.elem.byte_size()
            },
            &Ty::Struct {
                ..
            } => unimplemented!(),
            &Ty::Function(_) => panic!("function types are unsized!"),
            &Ty::Pointer(_) => {
                4
            },
        }
    }
    pub fn legalized_type(&self) -> (usize, Ty) {
        match self {
            &Ty::Vector(ref vt) => {
                let ty = VectorType {
                    count: vt.inner.per_legal_vty(),
                    inner: vt.inner,
                };
                (vt.split_parts(), Ty::Vector(ty))
            },
            _ => (1, self.clone()),
        }
    }
    pub fn get_pointer_to(&self) -> Ty {
        Ty::Pointer(Rc::new(self.clone()))
    }
    pub fn get_pointer_element(&self) -> Option<Ty> {
        match self {
            &Ty::Pointer(ref ty) => Some((&**ty).clone()),
            _ => None,
        }
    }
}
impl ::std::fmt::Display for Ty {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.llvm_type_str())
    }
}

pub trait TypeTrait {
    fn llvm_type_str(&self) -> String;
    fn legal_parts(&self) -> usize;
    fn legal_extra_parts(&self) -> usize { self.legal_parts() - 1 }
}
impl TypeTrait for Ty {
    fn llvm_type_str(&self) -> String {
        match self {
            &Ty::Void => "void".to_string(),
            &Ty::Scalar(ref ty) => ty.llvm_type_str().to_string(),
            &Ty::Vector(ref ty) => ty.llvm_type_str(),
            &Ty::Array(ref ty) => ty.llvm_type_str(),
            &Ty::Struct {
                ..
            } => {
                unimplemented!();
            },
            &Ty::Pointer(ref ty) => format!("{}*", ty.llvm_type_str()),
            &Ty::Function(ref fty) => {
                let mut str = fty.ret.llvm_type_str();

                str.push_str(" (");

                for (i, arg) in fty.args.iter().enumerate() {
                    if i != 0 {
                        str.push_str(", ");
                    }

                    str.push_str(&arg.llvm_type_str()[..]);
                }

                str.push_str(")");

                str
            },
        }
    }
    fn legal_parts(&self) -> usize {
        match self {
            &Ty::Vector(ref vty) => vty.split_parts(),
            _ => 1,
        }
    }
}
impl TypeTrait for Option<Ty> {
    fn llvm_type_str(&self) -> String {
        match self {
            &Some(ref ty) => ty.llvm_type_str(),
            &None => "void".to_string(),
        }
    }
    fn legal_parts(&self) -> usize {
        match self {
            &Some(ref ty) => ty.legal_parts(),
            &None => 1,
        }
    }
}
impl TypeTrait for Option<Rc<Ty>> {
    fn llvm_type_str(&self) -> String {
        match self {
            &Some(ref ty) => ty.llvm_type_str(),
            &None => "void".to_string(),
        }
    }
    fn legal_parts(&self) -> usize {
        match self {
            &Some(ref ty) => ty.legal_parts(),
            &None => 1,
        }
    }
}
// Yep.
pub fn min_align<T: Copy>(l: T, r: T) -> <<T as std::ops::BitOr>::Output as std::ops::BitAnd<<<<T as std::ops::BitOr>::Output as std::ops::Not>::Output as std::ops::Add>::Output>>::Output
    where T: std::ops::BitOr,
         <T as std::ops::BitOr>::Output: std::ops::BitAnd + std::ops::BitAnd<<<<T as std::ops::BitOr>::Output as std::ops::Not>::Output as std::ops::Add>::Output> + std::ops::Not,
        <<T as std::ops::BitOr>::Output as std::ops::Not>::Output: std::ops::Add + std::num::One
{
    (l | r) & (!(l | r) + std::num::One::one())
}

pub struct TrailingWhitespaceStripper {
    dest: &'static str,

    out: Option<Cursor<Vec<u8>>>,
}
impl std::io::Write for TrailingWhitespaceStripper {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.out.as_mut().unwrap().write(buf)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.out.as_mut().unwrap().flush()
    }
}
impl Drop for TrailingWhitespaceStripper {
    fn drop(&mut self) {
        let mut out = OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(self.dest)
            .unwrap();
        let text = self.out.take().unwrap().into_inner();
        let str = unsafe { String::from_utf8_unchecked(text) };

        for mut line in str.lines() {
            while line.ends_with(' ') {
                line = &line[..line.len() - 1];
            }

            out.write(line.as_ref()).unwrap();
            out.write("\n".as_ref()).unwrap();
        }
    }
}

fn open_ll(name: &'static str, desc: &'static str) -> RefCell<TrailingWhitespaceStripper> {
    let mut out = TrailingWhitespaceStripper {
        dest: name,
        out: Some(Cursor::new(vec!())),
    };

    writeln!(out, "; RUN: opt -S -pnacl-vector-canonicalization %s | FileCheck %s").unwrap();
    writeln!(out, "").unwrap();
    for line in desc.lines() {
        writeln!(out, "; {}", line).unwrap();
    }
    writeln!(out, "").unwrap();
    writeln!(out, "target datalayout = \"e-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-p:32:32:32-v128:32:128\"").unwrap();
    writeln!(out, "").unwrap();

    RefCell::new(out)
}
// TODO separate
enum StartingState {
    Checking {
        ret_names: Vec<usize>,
        arg_names: Vec<Vec<usize>>,
    },
    Defining {
        arg_names: Vec<usize>,
    },
}
impl StartingState {
    fn new_defining() -> StartingState {
        StartingState::Defining { arg_names: Vec::new(), }
    }
    fn new_checking() -> StartingState {
        StartingState::Checking {
            ret_names: Vec::new(),
            arg_names: Vec::new(),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Mode {
    Checking,
    Defining,
}

impl Mode {
    pub fn emit_prefix<T: Write>(&self, o: &mut T) {
        match self {
            &Mode::Checking => {
                write!(o, "; CHECK-NEXT:    ").unwrap();
            },
            &Mode::Defining => {
                write!(o, "  ").unwrap()
            },
        }
    }
    pub fn emit_label_prefix<T: Write>(&self, o: &mut T) {
        match self {
            &Mode::Checking => {
                write!(o, "; CHECK-LABEL: ").unwrap();
            },
            &Mode::Defining => { },
        }
    }
    pub fn emit_bb_prefix<T: Write>(&self, o: &mut T) {
        match self {
            &Mode::Checking => {
                write!(o, "; CHECK:       ").unwrap();
            },
            &Mode::Defining => { },
        }
    }
}

fn write_fn_start<T: Write>(o: &mut T, name: &str, ret: VectorType, args: &[VectorType],
                            n: &InstName, check: &mut StartingState) {
    n.reset();
    match check {
        &mut StartingState::Checking { ret_names: ref mut rets, arg_names: ref mut legal_args } => {
            let (ret_split_count, legal_retty) = ret.legalized_type();
            let legal_retllty = legal_retty.llvm_type_str();
            write!(o, "; CHECK-LABEL: define {to_ty} @{fn_name}(", fn_name=name, to_ty=legal_retllty).unwrap();

            for _ in (0..ret_split_count - 1) {
                rets.push(n.get());
                write!(o, "{}* nocapture nonnull dereferenceable(16), ",
                       legal_retllty).unwrap();
            }

            for (i, arg) in args.iter().enumerate() {
                let (split_count, legal_argty) = arg.legalized_type();
                let legal_argllty = legal_argty.llvm_type_str();
                let mut expanded_names = Vec::new();
                for i in (0..split_count) {
                    expanded_names.push(n.get());

                    write!(o, "{}{}", legal_argllty,
                           if i + 1 < split_count {
                               ", "
                           } else {
                               ""
                           }).unwrap();
                }

                if i + 1 < args.len() {
                    write!(o, ", ").unwrap();
                }

                legal_args.push(expanded_names);
            }
            writeln!(o, ")").unwrap();
        },
        &mut StartingState::Defining { ref mut arg_names } => {
            write!(o, "define {ret} @{name}(",
                   name=name, ret=ret.llvm_type_str()).unwrap();

            for (i, arg) in args.iter().enumerate() {
                arg_names.push(n.get());
                write!(o, "{}{}", arg.llvm_type_str(),
                       if i + 1 < args.len() {
                           ", "
                       } else {
                           ")"
                       }).unwrap();
            }

            writeln!(o, " {{").unwrap();
        },
    }
    n.get();
}

enum FinishingState {
    Checking {
        ret_arg_names: Vec<usize>,
        ret_names: Vec<usize>,
    },
    Defining {
        ret_name: usize,
    },
}
impl FinishingState {
    fn new_defining(last: usize) -> FinishingState {
        FinishingState::Defining { ret_name: last, }
    }
}

fn write_fn_finish<T: Write>(o: &mut T, ret: VectorType, check: FinishingState) {
    match check {
        FinishingState::Defining { ref ret_name } => {
            writeln!(o, "  ret {tty} %{n}", tty=ret.llvm_type_str(), n=ret_name).unwrap();
            writeln!(o, "}}").unwrap();
        },
        FinishingState::Checking {
            ref ret_names, ref ret_arg_names,
        } => {
            let (ret_split_count, legal_retty) = ret.legalized_type();
            let legal_retllty = legal_retty.llvm_type_str();

            assert!(ret_names.len() == ret_split_count,
                    "ret_names.len() != ret_split_count: {} != {}",
                    ret_names.len(), ret_split_count);
            assert!(ret_arg_names.len() == ret_split_count - 1,
                    "ret_arg_names.len() != ret_split_count - 1: {} != {}",
                    ret_arg_names.len(), ret_split_count - 1);

            for i in (0..ret_split_count - 1) {
                let ret = ret_arg_names[i];
                let part = ret_names[i + 1];

                writeln!(o, "; CHECK-NEXT:    store {tty} %{part}, {tty}* %{arg}, align 16",
                         tty=legal_retllty, part=part, arg=ret).unwrap();
            }

            writeln!(o, "; CHECK-NEXT:    ret {tty} %{last}",
                     tty=legal_retllty, last=ret_names[0]).unwrap();
        },
    }
}

pub type Name = usize;

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum Value {
    Named(usize),
    /// Includes the type
    Constant(String),

}
impl Value {
    /// self is already legal, migrate to LegalizedValue.
    pub fn mk_legalized(self) -> LegalizedValue {
        LegalizedValue::new(vec!(self))
    }
}
impl ::std::fmt::Display for Value {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            &Value::Named(name) => {
                write!(f, "%{}", name)
            },
            &Value::Constant(ref v) => {
                write!(f, "{}", v)
            },
        }
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct LegalizedValue(Vec<Value>);
impl LegalizedValue {
    pub fn new(v: Vec<Value>) -> LegalizedValue {
        LegalizedValue(v)
    }
}

thread_local!(static TEST_COUNT: Cell<u64> = Cell::new(0));

pub fn finished_generating_tests() {
    TEST_COUNT.with(|tc| {
        let tc = tc.get();

        println!("");
        println!("done ({} tests)!", tc);
    });
}

pub fn count_test(test_section: &'static str, name: &str) {
    let name = if name.starts_with('@') {
        &name[1..]
    } else {
        name
    };

    println!("creating {} test `{}`...", test_section, name);
    TEST_COUNT.with(|tc| tc.set(tc.get() + 1) );
}

const VECTOR_COUNTS: [usize; 7] = [2, 4, 6, 8, 12, 16, 20];
const ALIGNMENTS: [Option<usize>; 4] = [None, Some(1), Some(8), Some(32)];

pub mod ir;

pub mod phi_tests {
    use ir::*;

    use std::io::Write;

    use super::{VectorType, ScalarType, Mode, open_ll, count_test, Ty,
                VECTOR_COUNTS, SCALAR_TYPES};

    fn f<T: Write>(o: &mut T, count: usize, sty: ScalarType) {
        let vty = vector_type!(count, sty);
        let vty_ptr: Ty = vty.into();
        let vty_ptr = vty_ptr.get_pointer_to();
        let lvty = vty.legal_type();
        let lvty_ptr: Ty = lvty.into();
        let lvty_ptr = lvty_ptr.get_pointer_to();

        let name = format!("@phi_on_{}", vty.legal_name());
        count_test("phi", &name[..]);

        let mut d = Fun::new(name.clone());
        {
            let d_src = d.add_arg(vty_ptr.clone(), None);
            d.set_ret_ty(super::I32Ty.into());

            let entry = d.new_block("entry");
            let load = Inst::new_load(d_src, None, None);
            let load = entry.add_inst(load).unwrap();

            let undef = Val::new_undef(vty.into());

            let phi_bb = d.new_block("body");

            let br = Inst::new_uncond_br(&phi_bb);
            entry.add_inst(br);

            let cond_bb = d.new_block("cond");

            let phi = Inst::new_phi(vty.into(),
                                    vec!((load, entry.clone()),
                                         (undef, cond_bb.clone())));
            phi_bb.add_inst(phi);
            let br = Inst::new_uncond_br(&cond_bb);
            phi_bb.add_inst(br);

            let ret_bb = d.new_block("return");

            let br = Inst::new_cond_br(Val::new_const_true(),
                                       &ret_bb, &phi_bb);
            cond_bb.add_inst(br);

            let ret = Inst::new_ret(Val::new_const_i32(0));
            ret_bb.add_inst(ret);
        }

        let mut c = Fun::new(name);
        let c_src = c.add_arg(vty_ptr, None);
        c.set_ret_ty(super::I32Ty.into());

        let entry_bb = c.new_block("entry");
        let phi_bb = c.new_block("body");
        let cond_bb = c.new_block("cond");
        let ret_bb = c.new_block("return");

        let mut loads = Vec::new();
        let volatile = false;
        let alignment = None;
        if vty != lvty {
            let parts = vty.extra_parts();
            let parts = if vty.rem_last_split() == 0 {
                parts + 1
            } else {
                parts
            };
            for part in (0..parts) {
                let part_start = vty.inner.per_legal_vty() * part;
                let indices =
                    vec!(Val::new_const_i32(0),
                         Val::new_const_i32(part_start as i32));
                let gep = Inst::new_gep(c_src.clone(),
                                        &indices[..], false);
                let gep = entry_bb.add_inst(gep).unwrap();

                let bc = Inst::new_bitcast(gep, lvty_ptr.clone());
                let bc = entry_bb.add_inst(bc).unwrap();

                let alignment = alignment
                    .map(|a| super::min_align(a, vty.inner.size() * part_start) );
                let load = Inst::new_volatile_load(bc, alignment, None,
                                                   volatile);
                loads.push(entry_bb.add_inst(load).unwrap());
            }

            if vty.rem_last_split() != 0 {
                let last_part_start = parts * vty.inner.per_legal_vty();
                let last_part_len = vty.rem_last_split();
                let mut last = Some(Val::new_undef(lvty.into()));
                for idx in (0..last_part_len) {
                    let cidx = Val::new_const_i32((idx + last_part_start) as i32);
                    let indices = vec!(Val::new_const_i32(0), cidx);
                    let gep = Inst::new_gep(c_src.clone(),
                                            &indices[..],
                                            false);
                    let gep = entry_bb.add_inst(gep).unwrap();

                    let alignment = alignment
                        .map(|a| super::min_align(a, vty.inner.size() * (idx + last_part_start)) );

                    let load = Inst::new_volatile_load(gep, alignment, None,
                                                       volatile);
                    let load = entry_bb.add_inst(load).unwrap();

                    let cidx = Val::new_const_i32(idx as i32);
                    let inserted =
                        Inst::new_insertelement(last.take().unwrap(),
                                                load, cidx);
                    last = entry_bb.add_inst(inserted);
                }
                loads.push(last.unwrap());
            }
        } else {
            let load = Inst::new_volatile_load(c.arg_value(0), alignment, None, volatile);
            loads.push(entry_bb.add_inst(load).unwrap());
        }

        let br = Inst::new_uncond_br(&phi_bb);
        entry_bb.add_inst(br);

        for load in loads.into_iter() {
            let ty = load.ty();
            let phi = Inst::new_phi(ty.clone(),
                                    vec!((load, entry_bb.clone()),
                                         (Val::new_undef(ty), cond_bb.clone())));

            phi_bb.add_inst(phi);
        }

        let br = Inst::new_uncond_br(&cond_bb);
        phi_bb.add_inst(br);

        let br = Inst::new_cond_br(Val::new_const_true(),
                                   &ret_bb, &phi_bb);
        cond_bb.add_inst(br);

        let ret = Inst::new_ret(Val::new_const_i32(0));
        ret_bb.add_inst(ret);

        d.emit(o, Mode::Defining);
        c.emit(o, Mode::Checking);
        writeln!(o, "").unwrap();
    }

    pub fn main() {
        let out = open_ll("vector-canonicalization-phis.ll",
                          "Auto-generated tests for phi instructions.");
        let mut ob = out.borrow_mut();
        let o = &mut *ob;

        for &count in VECTOR_COUNTS.iter() {
            for &sty in SCALAR_TYPES.iter() {
                f(o, count, sty);
            }
        }
    }
}

pub mod load_tests {
    use ir::*;

    use std::io::Write;

    use super::{VectorType, ScalarType, Mode, open_ll, count_test, Ty,
                VECTOR_COUNTS, SCALAR_TYPES, ALIGNMENTS};

    fn f<T: Write>(o: &mut T, alignment: Option<usize>,
                   count: usize, sty: ScalarType,
                   volatile: bool) {
        let zero = Val::new_const_i32(0);

        let vty = vector_type!(count, sty);
        let vty_ptr: Ty = vty.into();
        let vty_ptr = vty_ptr.get_pointer_to();
        let lvty = vty.legal_type();
        let lvty_ptr: Ty = lvty.into();
        let lvty_ptr = lvty_ptr.get_pointer_to();

        let mut name = format!("@{}load_from_{}",
                               if volatile { "volatile_" }
                               else { "" },
                               vty.legal_name());
        if let Some(alignment) = alignment {
            name.push_str(&format!("_align_{}", alignment)[..]);
        } else {
            name.push_str("_unaligned");
        }
        count_test("load", &name[..]);

        let mut d = Fun::new(name.clone());

        let d_src = d.add_arg(vty_ptr.clone(), None);
        d.set_ret_ty(super::I32Ty.into());

        let load = Inst::new_volatile_load(d_src, alignment, None, volatile);
        d.add_inst(load);

        let ret = Inst::new_ret(zero.clone());
        d.add_inst(ret);

        let mut c = Fun::new(name);

        let c_src = c.add_arg(vty_ptr.clone(), None);
        c.set_ret_ty(super::I32Ty.into());

        if vty != lvty {
            let parts = vty.extra_parts();
            let parts = if vty.rem_last_split() == 0 {
                parts + 1
            } else {
                parts
            };
            for part in (0..parts) {
                let part_start = vty.inner.per_legal_vty() * part;
                let indices =
                    vec!(Val::new_const_i32(0),
                         Val::new_const_i32(part_start as i32));
                let gep = Inst::new_gep(c_src.clone(),
                                        &indices[..], false);
                let gep = c.add_inst(gep).unwrap();

                let bc = Inst::new_bitcast(gep, lvty_ptr.clone());
                let bc = c.add_inst(bc).unwrap();

                let alignment = alignment
                    .map(|a| super::min_align(a, vty.inner.size() * part_start) );
                let load = Inst::new_volatile_load(bc, alignment, None,
                                                   volatile);
                c.add_inst(load);
            }

            if vty.rem_last_split() != 0 {
                let last_part_start = parts * vty.inner.per_legal_vty();
                let last_part_len = vty.rem_last_split();
                let mut last = Some(Val::new_undef(lvty.into()));
                for idx in (0..last_part_len) {
                    let cidx = Val::new_const_i32((idx + last_part_start) as i32);
                    let indices = vec!(Val::new_const_i32(0), cidx);
                    let gep = Inst::new_gep(c_src.clone(),
                                            &indices[..],
                                            false);
                    let gep = c.add_inst(gep).unwrap();

                    let alignment = alignment
                        .map(|a| super::min_align(a, vty.inner.size() * (idx + last_part_start)) );

                    let load = Inst::new_volatile_load(gep, alignment, None,
                                                       volatile);
                    let load = c.add_inst(load).unwrap();

                    let cidx = Val::new_const_i32(idx as i32);
                    let inserted =
                        Inst::new_insertelement(last.take().unwrap(),
                                                load, cidx);
                    last = c.add_inst(inserted);
                }
            }
        } else {
            let load = Inst::new_volatile_load(c.arg_value(0), alignment, None, volatile);
            c.add_inst(load);
        }

        let ret = Inst::new_ret(zero.clone());
        c.add_inst(ret);

        d.emit(o, Mode::Defining);
        c.emit(o, Mode::Checking);
        writeln!(o, "").unwrap();
    }


    pub fn main() {
        let out = open_ll("vector-canonicalization-loads.ll",
                          "Auto-generated tests for load instructions.");
        let mut ob = out.borrow_mut();
        let o = &mut *ob;

        for &alignment in ALIGNMENTS.iter() {
            for &count in VECTOR_COUNTS.iter() {
                for &sty in SCALAR_TYPES.iter() {
                    f(o, alignment, count, sty, false);
                }
            }
        }
        for &alignment in ALIGNMENTS.iter() {
            for &count in VECTOR_COUNTS.iter() {
                for &sty in SCALAR_TYPES.iter() {
                    f(o, alignment, count, sty, true);
                }
            }
        }
    }

}

pub mod store_tests {
    use ir::*;

    use std::io::Write;

    use super::{VectorType, Mode, open_ll, count_test, Ty,
                VECTOR_COUNTS, SCALAR_TYPES, ALIGNMENTS,
                ScalarType};

    fn f<T: Write>(o: &mut T, alignment: Option<usize>,
                   count: usize, sty: ScalarType,
                   volatile: bool) {
        let zero = Val::new_const_i32(0);

        let vty = vector_type!(count, sty);
        let vty_ptr: Ty = vty.into();
        let vty_ptr = vty_ptr.get_pointer_to();
        let lvty = vty.legal_type();
        let lvty_ptr: Ty = lvty.into();
        let lvty_ptr = lvty_ptr.get_pointer_to();

        let mut name = format!("@{}store_to_{}",
                               if volatile { "volatile_" }
                               else { "" },
                               vty.legal_name());
        if let Some(alignment) = alignment {
            name.push_str(&format!("_align_{}", alignment)[..]);
        } else {
            name.push_str("_unaligned");
        }
        count_test("store", &name[..]);

        let mut d = Fun::new(name.clone());

        let d_dest = d.add_arg(vty_ptr.clone(), None);
        let d_src = d.add_arg(vty.into(), None);

        d.set_ret_ty(super::I32Ty.into());
        let store = Inst::new_volatile_store(d_src, d_dest, alignment,
                                             volatile);
        d.add_inst(store);

        let ret = Inst::new_ret(zero.clone());
        d.add_inst(ret);

        let mut c = Fun::new(name);

        let c_dest = c.add_arg(vty_ptr.clone(), None);
        for _ in (0..vty.split_parts()) {
            c.add_arg(lvty.into(), None);
        }
        c.set_ret_ty(super::I32Ty.into());

        if vty != lvty {
            let parts = vty.extra_parts();
            let parts = if vty.rem_last_split() == 0 {
                parts + 1
            } else {
                parts
            };
            for part in (0..parts) {
                let part_start = vty.inner.per_legal_vty() * part;
                let part_arg = c.arg_value(part + 1);
                let indices =
                    vec!(Val::new_const_i32(0),
                         Val::new_const_i32(part_start as i32));
                let gep = Inst::new_gep(c_dest.clone(),
                                        &indices[..], false);
                let gep = c.add_inst(gep).unwrap();

                let bc = Inst::new_bitcast(gep, lvty_ptr.clone());
                let bc = c.add_inst(bc).unwrap();

                let store_alignment = alignment
                    .map(|a| super::min_align(a, vty.inner.size() * part_start) );
                let store = Inst::new_volatile_store(part_arg, bc,
                                                     store_alignment,
                                                     volatile);
                c.add_inst(store);
            }

            if vty.rem_last_split() != 0 {
                let last_part_start = parts * vty.inner.per_legal_vty();
                let last_part_len = vty.rem_last_split();
                let last_part_arg = c.arg_value(parts + 1);
                for idx in (0..last_part_len) {
                    let cidx = Val::new_const_i32((idx + last_part_start) as i32);
                    let indices = vec!(Val::new_const_i32(0), cidx);
                    let gep = Inst::new_gep(c_dest.clone(),
                                            &indices[..],
                                            false);
                    let gep = c.add_inst(gep).unwrap();

                    let cidx = Val::new_const_i32(idx as i32);
                    let extracted =
                        Inst::new_extractelement(last_part_arg.clone(),
                                                 cidx.clone());
                    let extracted = c.add_inst(extracted).unwrap();

                    let store_alignment = alignment
                        .map(|a| super::min_align(a, vty.inner.size() * (idx + last_part_start)) );

                    let store = Inst::new_volatile_store(extracted, gep,
                                                         store_alignment,
                                                         volatile);
                    c.add_inst(store);
                }
            }
        } else {
            let store = Inst::new_volatile_store(c.arg_value(1), c.arg_value(0),
                                                 alignment, volatile);
            c.add_inst(store);
        }

        let ret = Inst::new_ret(zero.clone());
        c.add_inst(ret);

        d.emit(o, Mode::Defining);
        c.emit(o, Mode::Checking);
        writeln!(o, "").unwrap();
    }

    pub fn main() {
        let out = open_ll("vector-canonicalization-stores.ll",
                          "Auto-generated tests for store instructions.");
        let mut ob = out.borrow_mut();
        let o = &mut *ob;

        for &alignment in ALIGNMENTS.iter() {
            for &count in VECTOR_COUNTS.iter() {
                for &sty in SCALAR_TYPES.iter() {
                    f(o, alignment, count, sty, false);
                }
            }
        }
        for &alignment in ALIGNMENTS.iter() {
            for &count in VECTOR_COUNTS.iter() {
                for &sty in SCALAR_TYPES.iter() {
                    f(o, alignment, count, sty, true);
                }
            }
        }
    }
}

pub mod insert_tests {
    use ir::*;

    use std::io::Write;

    use super::{VectorType, Mode, open_ll, count_test, Ty,
                VECTOR_COUNTS, SCALAR_TYPES};

    pub fn main() {
        let out = open_ll("vector-canonicalization-inserts.ll",
                          "Auto-generated tests for insertelement instructions.");
        let mut ob = out.borrow_mut();
        let o = &mut *ob;

        for &count in VECTOR_COUNTS.iter() {
            for &sty in SCALAR_TYPES.iter() {
                let vty = vector_type!(count, sty);
                let lvty = vty.legal_type();
                let lvty_ptr: Ty = lvty.into();
                let lvty_ptr = lvty_ptr.get_pointer_to();

                for idx in (0..count + 1) {
                    let d_idx_v = Val::new_const(super::I32Ty.into(),
                                                 format!("{}", idx));
                    let c_idx_v = Val::new_const(super::I32Ty.into(),
                                                 format!("{}", vty.part_index(idx)));

                    let name = if idx != count {
                        format!("@insert_{}_at_{}", vty.legal_name(),
                                idx)
                    } else {
                        format!("@insert_{}_undef_idx", vty.legal_name())
                    };
                    count_test("insertelement", &name[..]);

                    let mut d = Fun::new(name.clone());
                    let mut c = Fun::new(name.clone());

                    d.set_ret_ty(vty.into());
                    c.set_ret_ty(lvty.into());

                    for _ in (0..vty.extra_parts()) {
                        let attrs = Attrs {
                            no_capture: true,
                            non_null: true,
                            dereferenceable: Some(16),
                            .. Default::default()
                        };
                        c.add_arg(lvty_ptr.clone(), Some(attrs));
                    }

                    let d_from_arg = d.add_arg(vty.into(), None);
                    let d_insert_arg = d.add_arg(vty.inner.into(), None);

                    let mut c_from_arg = Vec::new();
                    for _ in (0..vty.split_parts()) {
                        let a = c.add_arg(lvty.into(), None);
                        c_from_arg.push(a);
                    }
                    let c_insert_arg = c.add_arg(vty.inner.into(), None);

                    let insert = Inst::new_insertelement(d_from_arg, d_insert_arg, d_idx_v);
                    let ret = d.add_inst(insert).unwrap();
                    let ret = Inst::new_ret(ret);
                    d.add_inst(ret);

                    if vty == lvty {
                        assert_eq!(c_from_arg.len(), 1);
                        let insert = Inst::new_insertelement(c_from_arg[0].clone(), c_insert_arg, c_idx_v);
                        let ret = c.add_inst(insert).unwrap();
                        let ret = Inst::new_ret(ret);
                        c.add_inst(ret);
                    } else {
                        let mut stores = Vec::new();
                        for (i, from) in c_from_arg.into_iter().enumerate() {
                            let v = if i == vty.split_part(idx) && idx < vty.count() {
                                let insert = Inst::new_insertelement(from,
                                                                     c_insert_arg.clone(),
                                                                     c_idx_v.clone());
                                c.add_inst(insert).unwrap()
                            } else {
                                from
                            };

                            if i == 0 {
                                let r = Inst::new_ret(v);
                                stores.push(r);
                            } else {
                                let s = Inst::new_store(v, c.arg_value(i - 1), Some(16));
                                stores.push(s);
                            }
                        }

                        for s in stores[1..].iter() {
                            c.add_inst(s.clone());
                        }
                        c.add_inst(stores[0].clone());
                    }

                    d.emit(o, Mode::Defining);
                    c.emit(o, Mode::Checking);
                    writeln!(o, "").unwrap();
                }
            }
        }

        for &count in VECTOR_COUNTS.iter() {
            for &sty in SCALAR_TYPES.iter() {
                let vty = vector_type!(count, sty);
                let lvty = vty.legal_type();
                let lvty_ptr: Ty = lvty.into();
                let lvty_ptr = lvty_ptr.get_pointer_to();

                let name = format!("@insert_{}_var_idx", vty.legal_name());
                count_test("insertelement", &name[..]);

                let mut d = Fun::new(name.clone());
                let mut c = Fun::new(name.clone());

                d.set_ret_ty(vty.into());
                c.set_ret_ty(lvty.into());

                for _ in (0..vty.extra_parts()) {
                    let attrs = Attrs {
                        no_capture: true,
                        non_null: true,
                        dereferenceable: Some(16),
                        .. Default::default()
                    };
                    c.add_arg(lvty_ptr.clone(), Some(attrs));
                }

                let d_from_arg = d.add_arg(vty.into(), None);
                let d_insert_arg = d.add_arg(vty.inner.into(), None);
                let d_idx_v = d.add_arg(super::I32Ty.into(), None);

                let mut c_from_arg = Vec::new();
                for _ in (0..vty.split_parts()) {
                    let a = c.add_arg(lvty.into(), None);
                    c_from_arg.push(a);
                }
                let c_insert_arg = c.add_arg(vty.inner.into(), None);
                let c_idx_v = c.add_arg(super::I32Ty.into(), None);

                let insert = Inst::new_insertelement(d_from_arg, d_insert_arg, d_idx_v);
                let ret = d.add_inst(insert).unwrap();
                let ret = Inst::new_ret(ret);
                d.add_inst(ret);

                if vty.extra_parts() == 0 {
                    assert_eq!(c_from_arg.len(), 1);
                    let e = Inst::new_insertelement(c_from_arg[0].clone(),
                                                    c_insert_arg,
                                                    c_idx_v);
                    let inserted = c.add_inst(e).unwrap();
                    c.add_inst(Inst::new_ret(inserted));
                } else {
                    let mut stores = Vec::new();
                    let per_part = vty.inner.per_legal_vty();
                    for (i, from) in c_from_arg.into_iter().enumerate() {
                        let start = i * per_part;
                        let per = ::std::cmp::min(vty.count() - i * per_part, per_part);

                        let mut last_inserted = Some(from);
                        for idx in (0..per) {
                            let param_idx = Val::new_const_i32((idx + start) as i32);
                            let part_idx = Val::new_const_i32(idx as i32);

                            let last = last_inserted.take().unwrap();

                            let e = Inst::new_insertelement(last.clone(), c_insert_arg.clone(),
                                                            part_idx);
                            let inserted = c.add_inst(e).unwrap();
                            let cmp = Inst::new_cmp(Cmp::Int(IntPred::Eq), param_idx,
                                                    c_idx_v.clone());
                            let cmp = c.add_inst(cmp).unwrap();
                            let selected = Inst::new_select(cmp, inserted, last);
                            last_inserted = c.add_inst(selected);
                        }
                        let v = last_inserted.unwrap();

                        if i == 0 {
                            let r = Inst::new_ret(v);
                            stores.push(r);
                        } else {
                            let s = Inst::new_store(v, c.arg_value(i - 1), Some(16));
                            stores.push(s);
                        }
                    }

                    for s in stores[1..].iter() {
                        c.add_inst(s.clone());
                    }
                    c.add_inst(stores[0].clone());
                }

                d.emit(o, Mode::Defining);
                c.emit(o, Mode::Checking);
                writeln!(o, "").unwrap();
            }
        }
    }
}

pub mod extract_tests {
    use ir::*;

    use std::io::Write;

    use super::{VectorType, Mode, open_ll, count_test,
                VECTOR_COUNTS, SCALAR_TYPES};

    pub fn main() {
        let out = open_ll("vector-canonicalization-extracts.ll",
                          "Auto-generated tests for extractelement instructions.");
        let mut ob = out.borrow_mut();
        let o = &mut *ob;

        for &count in VECTOR_COUNTS.iter() {
            for &sty in SCALAR_TYPES.iter() {
                let vty = vector_type!(count, sty);
                let lvty = vty.legal_type();

                for idx in (0..count + 1) {
                    let d_idx_v = Val::new_const(super::I32Ty.into(),
                                                 format!("{}", idx));
                    let c_idx_v = Val::new_const(super::I32Ty.into(),
                                                 format!("{}", vty.part_index(idx)));

                    let name = if idx != count {
                        format!("@extract_{}_at_{}", vty.legal_name(),
                                idx)
                    } else {
                        format!("@extract_{}_undef_idx", vty.legal_name())
                    };
                    count_test("extractelement", &name[..]);

                    let mut d = Fun::new(name.clone());
                    let mut c = Fun::new(name.clone());

                    d.set_ret_ty(sty.into());
                    c.set_ret_ty(sty.into());

                    let d_from_arg = d.add_arg(vty.into(), None);
                    let mut c_from_arg = None;
                    for i in (0..vty.split_parts()) {
                        let a = c.add_arg(lvty.into(), None);
                        if vty.split_part(idx) == i {
                            c_from_arg = Some(a);
                        }
                    }
                    let c_from_arg = c_from_arg.unwrap();

                    let extract = Inst::new_extractelement(d_from_arg, d_idx_v);
                    let ret = d.add_inst(extract).unwrap();
                    let ret = Inst::new_ret(ret);
                    d.add_inst(ret);

                    let extract = Inst::new_extractelement(c_from_arg, c_idx_v);
                    let ret = c.add_inst(extract).unwrap();
                    let ret = Inst::new_ret(ret);
                    c.add_inst(ret);


                    d.emit(o, Mode::Defining);
                    c.emit(o, Mode::Checking);
                    writeln!(o, "").unwrap();
                }
            }
        }

        for &count in VECTOR_COUNTS.iter() {
            for &sty in SCALAR_TYPES.iter() {
                let vty = vector_type!(count, sty);
                let lvty = vty.legal_type();

                let name = format!("@extract_{}_var_idx", vty.legal_name());
                count_test("extractelement", &name[..]);

                let mut d = Fun::new(name.clone());
                let mut c = Fun::new(name.clone());

                d.set_ret_ty(sty.into());
                c.set_ret_ty(sty.into());

                let d_from_arg = d.add_arg(vty.into(), None);
                let d_idx_v = d.add_arg(super::I32Ty.into(), None);

                let mut c_from_arg = Vec::new();
                for _ in (0..vty.split_parts()) {
                    let a = c.add_arg(lvty.into(), None);
                    c_from_arg.push(a);
                }
                let c_idx_v = c.add_arg(super::I32Ty.into(), None);

                let extract = Inst::new_extractelement(d_from_arg, d_idx_v);
                let ret = d.add_inst(extract).unwrap();
                let ret = Inst::new_ret(ret);
                d.add_inst(ret);

                if vty.extra_parts() == 0 {
                    assert_eq!(c_from_arg.len(), 1);
                    let extract = Inst::new_extractelement(c_from_arg[0].clone(),
                                                           c_idx_v);
                    let ret = c.add_inst(extract).unwrap();
                    let ret = Inst::new_ret(ret);
                    c.add_inst(ret);
                } else {
                    let per_part = vty.inner.per_legal_vty();
                    let mut last_extracted = Some(Val::new_undef(vty.inner.into()));
                    for part in (0..vty.split_parts()) {
                        let start = part * per_part;
                        let per = ::std::cmp::min(vty.count() - part * per_part, per_part);
                        let from = &c_from_arg[part];

                        for idx in (0..per) {
                            let param_idx = Val::new_const_i32((idx + start) as i32);
                            let part_idx = Val::new_const_i32(idx as i32);

                            let last = last_extracted.take().unwrap();

                            let e = Inst::new_extractelement(from.clone(), part_idx);
                            let extracted = c.add_inst(e).unwrap();
                            let cmp = Inst::new_cmp(Cmp::Int(IntPred::Eq), param_idx,
                                                    c_idx_v.clone());
                            let cmp = c.add_inst(cmp).unwrap();
                            let selected = Inst::new_select(cmp, extracted, last);
                            last_extracted = c.add_inst(selected);
                        }
                    }
                    let ret = Inst::new_ret(last_extracted.unwrap());
                    c.add_inst(ret);
                }

                d.emit(o, Mode::Defining);
                c.emit(o, Mode::Checking);
                writeln!(o, "").unwrap();
            }
        }
    }
}

pub mod cmp_tests {
    use ir::*;

    use std::io::Write;
    use std::rc::Rc;

    use super::{VectorType, Ty, Mode, open_ll, count_test,
                VECTOR_COUNTS, SCALAR_TYPES};

    pub fn main() {
        let out = open_ll("vector-canonicalization-cmps.ll",
                          "Auto-generated tests for cmp instructions.");
        let mut ob = out.borrow_mut();
        let o = &mut *ob;

        struct F {
            vty: VectorType,

            d_cmps: Option<Value>,
            c_cmps: Option<Vec<Value>>,

            d: Fun,
            c: Fun,
        }
        impl F {
            fn start(name: String, vty: VectorType, lvty: VectorType,
                     lvty_ptr: &Ty) -> F {

                count_test("cmp", &name[..]);

                let mut d = Fun::new(name.clone());
                let mut c = Fun::new(name.clone());

                d.set_ret_ty(vty.into());
                c.set_ret_ty(lvty.into());

                for _ in (0..vty.extra_parts()) {
                    let attrs = Attrs {
                        no_capture: true,
                        non_null: true,
                        dereferenceable: Some(16),
                        .. Default::default()
                    };
                    c.add_arg(lvty_ptr.clone(), Some(attrs));
                }

                for _ in (0..4) {
                    d.add_arg(vty.into(), None);
                    for _ in (0..vty.split_parts()) {
                        c.add_arg(lvty.into(), None);
                    }
                }

                F {
                    vty: vty,

                    d_cmps: None,
                    c_cmps: None,

                    d: d,
                    c: c,
                }
            }

            fn middle(&mut self, cmp: Cmp) {
                let d_cmp = Inst::new_cmp(cmp,
                                          self.d.arg_value(0),
                                          self.d.arg_value(1));
                self.d_cmps = self.d.add_inst(d_cmp);

                let mut ccmps = Vec::new();
                for part in (0..self.vty.split_parts()) {
                    let left = self.c.arg_value(self.vty.extra_parts() + part);
                    let right = self.c.arg_value(self.vty.extra_parts() + part + self.vty.split_parts());

                    let cmp = Inst::new_cmp(cmp, left, right);
                    ccmps.push(self.c.add_inst(cmp).unwrap());
                }
                self.c_cmps = Some(ccmps);

            }

            fn finish(&mut self) {
                let d_cmps = self.d_cmps.take().unwrap();
                let c_cmps = self.c_cmps.take().unwrap();

                let d_select = Inst::new_select(d_cmps, self.d.arg_value(2),
                                                self.d.arg_value(3));
                let d_selv = self.d.add_inst(d_select).unwrap();
                let d_ret = Inst::new_ret(d_selv);
                self.d.add_inst(d_ret);

                assert_eq!(c_cmps.len(), self.vty.split_parts());
                let mut c_selects = Vec::new();
                for (i, cmp) in c_cmps.into_iter().enumerate() {
                    let left = self.c.arg_value(self.vty.extra_parts() + self.vty.split_parts() * 2 + i);
                    let right = self.c.arg_value(self.vty.extra_parts() + self.vty.split_parts() * 3 + i);

                    let s = Inst::new_select(cmp, left, right);
                    c_selects.push(self.c.add_inst(s).unwrap());
                }

                self.c.create_split_ret_stores(c_selects.as_ref());
            }

            fn emit<T: Write>(&self, o: &mut T) {
                self.d.emit(o, Mode::Defining);
                self.c.emit(o, Mode::Checking);
                writeln!(o, "").unwrap();
            }
        }

        for &count in VECTOR_COUNTS.iter() {
            for &sty in SCALAR_TYPES.iter() {
                if sty.is_fpty() {
                    let vty = vector_type!(count, sty);
                    let lvty = vty.legal_type();
                    let lvty_ptr = Ty::Pointer(Rc::new(Ty::Vector(lvty)));

                    for &pred in FpPred::permutations().iter() {
                        for &attrs in FastMathAttrs::permutations().iter() {
                            let name = format!("@fcmp_{}_on_{}{}", pred,
                                               vty.legal_name(),
                                               attrs.fn_name_str());

                            let mut f = F::start(name, vty, lvty, &lvty_ptr);
                            f.middle(Cmp::Fp(pred, attrs));
                            f.finish();
                            f.emit(o);
                        }
                    }
                }
            }
        }
        for &count in VECTOR_COUNTS.iter() {
            for &sty in SCALAR_TYPES.iter() {
                if sty.is_intty() {
                    let vty = vector_type!(count, sty);
                    let lvty = vty.legal_type();
                    let lvty_ptr = Ty::Pointer(Rc::new(Ty::Vector(lvty)));

                    for &pred in IntPred::permutations().iter() {
                        let name = format!("@icmp_{}_on_{}", pred,
                                           vty.legal_name());

                        let mut f = F::start(name, vty, lvty, &lvty_ptr);
                        f.middle(Cmp::Int(pred));
                        f.finish();
                        f.emit(o);
                    }
                }
            }
        }
    }
}

pub mod call_tests {
    use ir::*;

    //use std::cell::{RefCell};
    //use std::collections::HashMap;
    use std::io::Write;
    use std::rc::Rc;

    //use rand::{StdRng, SeedableRng, Rng};

    use super::{VectorType, Ty, InstName, Mode, TypeTrait, open_ll,
                count_test,
                VECTOR_COUNTS, SCALAR_TYPES, FunctionType};

    pub fn main() {
        let out = open_ll("vector-canonicalization-calls.ll",
                          "Auto-generated tests for call instructions.");

        //let seed: &[_] = &[4, 3, 2, 1]; // so we always generate the same sequence.
        //let rng: StdRng = SeedableRng::from_seed(seed);

        let fun_namer = InstName::new();

        fn create_split_ret_allocas(f: &mut Fun, ret: &Ty) -> Vec<Value> {
            let mut extra_rets = Vec::new();
            match ret {
                &Ty::Vector(ref vty) => {
                    let lvty = vty.legal_type();
                    for _ in (0..vty.extra_parts()) {
                        let a = Inst::new_alloca(lvty.to_generic_ty(), None, Some(16));
                        let v = f.add_inst(a).unwrap();
                        extra_rets.push(v);
                    }
                },
                _ => {},
            }
            extra_rets
        }
        fn create_split_ret_stores(f: &mut Fun, vals: &[Value]) {
            f.create_split_ret_stores(vals)
        }
        fn create_split_ret_loads(f: &mut Fun, original_rty: Ty,
                                  call: Instruction) -> Vec<Value> {
            let mut out = Vec::new();
            out.push(call.get_value());

            let parts = original_rty.legal_parts();
            for i in (0..parts - 1) {
                let op = call.get_operand(i + 1);

                let inst = Inst::new_load(op, Some(16), None);
                out.push(inst.get_value());
                f.add_inst(inst);
            }

            out
        }

        let mut ob = out.borrow_mut();
        let o = &mut *ob;
        let mut permutations = Vec::new();
        for &count in VECTOR_COUNTS.iter() {
            for &ty in SCALAR_TYPES.iter() {
                let vty = vector_type!(count, ty);

                let name = format!("@fn_{}_{}", fun_namer.get(),
                                   vty.legal_name());
                count_test("call", &name[..]);

                let mut d = Fun::new(name.clone());
                let arg = d.add_arg(Ty::Vector(vty.clone()), None);
                d.set_ret_ty(Ty::Vector(vty.clone()));

                let dv = d.build_value();

                let call = Inst::new_call(dv.clone(), &[arg.clone()],
                                          None);
                let callv = d.add_inst(call)
                    .unwrap();

                let ret = Inst::new_ret(callv);
                d.add_inst(ret);
                d.emit(o, Mode::Defining);

                let mut c = Fun::new(name.clone());
                let lvty = vty.legal_type();
                let lvty_ptr = Ty::Pointer(Rc::new(Ty::Vector(lvty)));
                for _ in (0..vty.extra_parts()) {
                    let attrs = Attrs {
                        no_capture: true,
                        non_null: true,
                        dereferenceable: Some(16),
                        .. Default::default()
                    };
                    c.add_arg(lvty_ptr.clone(), Some(attrs));
                }
                for _ in (0..vty.split_parts()) {
                    c.add_arg(Ty::Vector(lvty), None);
                }
                c.set_ret_ty(Ty::Vector(lvty));
                let cv = c.build_value();

                let extra_rets = create_split_ret_allocas(&mut c, &Ty::Vector(vty));
                let mut call_args = Vec::new();
                let mut call_attrs = Vec::new();
                call_args.extend(extra_rets.iter().map(|v| v.clone() ));
                for _ in (0..call_args.len()) {
                    call_attrs.push(Attrs::new_split());
                }
                for i in (vty.extra_parts()..vty.extra_parts() + vty.split_parts()) {
                    call_args.push(c.arg_value(i));
                    call_attrs.push(Default::default());
                }
                let call = Inst::new_call(cv.clone(), &call_args[..],
                                          Some(call_attrs.as_ref()));
                c.add_inst(call.clone()).unwrap();

                let ret_loads = create_split_ret_loads(&mut c, Ty::Vector(vty),
                                                       call);
                create_split_ret_stores(&mut c, &ret_loads[..]);

                c.emit(o, Mode::Checking);

                writeln!(o, "").unwrap();

                permutations.push((vty, dv, cv))
            }
        }

        fn fix_fty(FunctionType { ret, args }: FunctionType) -> FunctionType {
            let mut out: FunctionType = Default::default();

            if let Some(ret) = ret {
                let (parts, lty) = ret.legalized_type();
                let lty_ptr = lty.get_pointer_to();
                out.ret = Some(lty);
                for _ in (0..parts - 1) {
                    out.args.push(lty_ptr.clone());
                }
            }

            for a in args.into_iter() {
                let (parts, lty) = a.legalized_type();
                if parts == 1 {
                    out.args.push(lty);
                } else {
                    for _ in (0..parts) {
                        out.args.push(lty.clone());
                    }
                }
            };
            out
        }

        for (vty, odv, ocv) in permutations.into_iter() {
            let name = format!("@fn_{}_{}_call_arg", fun_namer.get(),
                               vty.legal_name());
            count_test("call", &name[..]);

            let mut d = Fun::new(name.clone());
            let to_call = d.add_arg(odv.ty().clone(), None);
            let original_to_call_ty = to_call.ty();
            let arg = d.add_arg(Ty::Vector(vty.clone()), None);
            d.set_ret_ty(Ty::Vector(vty.clone()));

            let dv = d.build_value();

            let call1 = Inst::new_call(to_call, &[arg.clone()],
                                       None);
            let call1v = d.add_inst(call1)
                .unwrap();

            let call2 = Inst::new_call(dv.clone(), &[odv.clone(),
                                                     call1v.clone()],
                                       None);
            let call2v = d.add_inst(call2)
                .unwrap();

            let ret = Inst::new_ret(call2v);
            d.add_inst(ret);
            d.emit(o, Mode::Defining);

            let mut c = Fun::new(name.clone());
            let lvty = vty.legal_type();
            let lvty_ptr = Ty::Pointer(Rc::new(Ty::Vector(lvty)));
            for _ in (0..vty.extra_parts()) {
                let attrs = Attrs {
                    no_capture: true,
                    non_null: true,
                    dereferenceable: Some(16),
                    .. Default::default()
                };
                c.add_arg(lvty_ptr.clone(), Some(attrs));
            }
            let to_call = c.add_arg(odv.ty().clone(), None);
            for _ in (0..vty.split_parts()) {
                c.add_arg(Ty::Vector(lvty), None);
            }
            c.set_ret_ty(Ty::Vector(lvty));
            let cv = c.build_value();

            let extra_rets = create_split_ret_allocas(&mut c, &Ty::Vector(vty));

            let original_to_call_fty = match original_to_call_ty.get_pointer_element() {
                Some(Ty::Function(ref fty)) => (&**fty).clone(),
                _ => unreachable!(),
            };
            let call1v_lty: Ty = fix_fty(original_to_call_fty).into();
            let call1v_lty_ptr = call1v_lty.get_pointer_to();
            let to_call = if call1v_lty_ptr != to_call.ty() {
                let bitcast = Inst::new_bitcast(to_call, call1v_lty_ptr);
                c.add_inst(bitcast).unwrap()
            } else {
                to_call
            };

            let mut call_args = Vec::new();
            let mut call_attrs = Vec::new();
            call_args.extend(extra_rets.iter().map(|v| v.clone() ));
            for _ in (0..call_args.len()) {
                call_attrs.push(Attrs::new_split());
            }
            for i in (vty.extra_parts()..vty.extra_parts() + vty.split_parts()) {
                call_args.push(c.arg_value(i + 1));
                call_attrs.push(Default::default());
            }
            let call = Inst::new_call(to_call, &call_args[..],
                                      Some(call_attrs.as_ref()));
            c.add_inst(call.clone()).unwrap();

            let ret_loads = create_split_ret_loads(&mut c, Ty::Vector(vty),
                                                   call);

            let mut call_args = Vec::new();
            let mut call_attrs = Vec::new();
            call_args.extend(extra_rets.iter().map(|v| v.clone() ));
            for _ in (0..call_args.len()) {
                call_attrs.push(Attrs::new_split());
            }
            let bitcast = if ocv.ty() != odv.ty() {
                Val::new_const_bitcast(ocv, odv.ty())
            } else {
                ocv
            };
            call_args.push(bitcast);
            call_attrs.push(Default::default());
            for _ in (0..ret_loads.len()) {
                call_attrs.push(Default::default());
            }
            call_args.extend(ret_loads.into_iter());

            let call = Inst::new_call(cv, &call_args[..], Some(call_attrs.as_ref()));
            c.add_inst(call.clone()).unwrap();

            let ret_loads = create_split_ret_loads(&mut c, Ty::Vector(vty),
                                                   call);

            create_split_ret_stores(&mut c, &ret_loads[..]);

            c.emit(o, Mode::Checking);

            writeln!(o, "").unwrap();
        }

        return;

        // TODO?

        /*const SCALARS: [ScalarType; 6] = [super::I8Ty, super::I16Ty, super::I32Ty,
                                          super::I64Ty, super::F32Ty, super::F64Ty];

        struct D {
            d: Rc<RefCell<Fun>>,
            c: Rc<RefCell<Fun>>,
        }

        let funs: HashMap<FunctionType, D> = HashMap::new();
        //let funs = RefCell::new(funs);

        const FUNCTION_TYPE_ID: usize = 3;

        struct Gen {
            rng: StdRng,
        }
        impl Gen {
            fn scalar_type(&mut self) -> Ty {
                self.scalar().into()
            }
            fn scalar(&mut self) -> ScalarType {
                self.rng
                    .choose(SCALARS.as_ref())
                    .unwrap()
                    .clone()
            }

            fn function(&mut self, depth: usize) -> FunctionType {
                FunctionType {
                    ret: if self.rng.gen_weighted_bool(2) {
                        Some(self.rand_type(depth + 1))
                    } else {
                        None
                    },

                    args: {
                        let count = self.rng.gen_range(0, 12);
                        let mut args = Vec::new();
                        for _ in (0..count) {
                            args.push(self.rand_type(depth + 1));
                        }
                        args
                    },
                }
            }

            fn gen_type(&mut self, type_id: usize, depth: usize) -> Ty {
                match type_id {
                    0 => self.scalar_type(),
                    1 => {
                        let count = self.rng.gen_range(0, 32);
                        let inner = self.rand_type(depth + 1);
                        let aty = ArrayType {
                            count: count,
                            elem: inner,
                        };
                        aty.into()
                    },
                    2 => self.rand_type(depth + 1).get_pointer_to(),
                    FUNCTION_TYPE_ID => self.function(depth + 1).into(),
                    _ => {
                        let count = self.rng.gen_range(1, 21);
                        let inner = self.scalar();
                        vector_type!(count, inner).into()
                    },
                }
            }
            fn rand_type(&mut self, depth: usize) -> Ty {
                if depth >= 3 {
                    self.scalar_type()
                } else {
                    let ty = self.rng.gen_range::<usize>(0, 10);
                    self.gen_type(ty, depth)
                }
            }
        }

        let mut ty_gen = Gen {
            rng: rng,
        };

        for _ in (0..20) {
            let name = format!("@fn_{}", fun_namer.get());
            println!("creating call test `{}`", &name[1..]);

            let dfty = ty_gen.function(0);
            let mut d = Fun::new_with_ty(name.clone(), dfty.clone());
            let ret;
            match dfty.ret {
                Some(Ty::Void) | None => {
                    ret = Inst::new_ret(Val::new_const(Ty::Void, "".to_string()));
                },
                Some(ref ty) => {
                    ret = Inst::new_ret(Val::new_const(ty.clone(), "undef".to_string()));
                },
            }
            d.add_inst(ret);

            d.emit(o, Mode::Defining);

            let c = Fun::new(name.clone());

            let v = D {
                d: Rc::new(RefCell::new(d)),
                c: Rc::new(RefCell::new(c)),
            };


        }*/
    }
}
pub mod shuffle_tests {
    use std::cmp::min;
    use std::io::Write;

    use rand::{Rng, SeedableRng, StdRng};

    use super::{VectorType, Value, Mode, Name,
                LegalizedValue, InstName, StartingState,
                FinishingState};
    use super::{open_ll, write_fn_start, write_fn_finish,
                count_test};

    struct Shuffle {
        ty: VectorType,
        mask: Vec<i32>,
    }

    macro_rules! shuffle_inst (
        ($ty:expr => [$($mask:expr),*]) => {
            Shuffle::new($ty, vec!($($mask),*))
        }
    );

    impl Shuffle {
        fn new(ty: VectorType, mask: Vec<i32>) -> Shuffle {
            for &index in mask.iter() {
                if index >= (ty.count() * 2) as i32 {
                    println!("index = {}, ty = {}",
                             index, ty.llvm_type_str());
                }
                debug_assert!(index < (ty.count() * 2) as i32);
            }

            Shuffle {
                ty: ty, mask: mask,
            }
        }

        fn result_ty(&self) -> VectorType {
            VectorType::new(self.mask.len(), self.ty.inner)
        }

        fn emit<T: Write>(&self, o: &mut T, name: Name, left: Value, right: Value, mode: Mode) {
            mode.emit_prefix(o);
            write!(o, "%{name} = shufflevector {ty} {left}, {ty} {right}, <{mask_len} x i32> ",
                   name=name, left=left, right=right, ty=self.ty.llvm_type_str(),
                   mask_len=self.mask.len())
                .unwrap();

            if self.mask.iter().all(|&m| m == 0 ) {
                writeln!(o, "zeroinitializer").unwrap();
            } else {
                write!(o, "<").unwrap();
                for (i, &m) in self.mask.iter().enumerate() {
                    write!(o, "i32 {}", m).unwrap();

                    if i + 1 < self.mask.len() {
                        write!(o, ", ").unwrap();
                    }
                }
                writeln!(o, ">").unwrap();
            }

            o.flush().unwrap();
        }

        /// This is basically a duplication of the logic we're testing :/
        fn emit_checking<T: Write>(&self, o: &mut T,
                                   left: LegalizedValue,
                                   right: LegalizedValue,
                                   n: &InstName) -> LegalizedValue {
            let result_ty = self.result_ty();

            if self.mask.iter().enumerate().all(|(i, &m)| i == m as usize ) {
                let i = left.0
                    .into_iter()
                    .chain(right.0.into_iter());
                let mut out = Vec::new();
                let mut parts_left = result_ty.split_parts();
                for part in i {
                    if parts_left == 0 { break; }

                    out.push(part);
                    parts_left -= 1;
                }

                return LegalizedValue(out);
            }

            const MODE: Mode = Mode::Checking;

            let (split_count, legal_ty) = result_ty.legalized_type();
            if legal_ty == result_ty && legal_ty == self.ty {
                let name = n.get();
                self.emit(o, name, left.0[0].clone(),
                          right.0[0].clone(),
                          MODE);

                return LegalizedValue(vec!(Value::Named(name)));
            }
            let per = legal_ty.inner.per_legal_vty();

            let original_count = self.ty.count();

            let undef = Value::Constant("undef".to_string());
            let mut out = Vec::new();

            for i in (0..split_count) {
                let mut shuffle = Shuffle {
                    ty: legal_ty,
                    mask: Vec::new(),
                };

                let start = i * per;
                let end = min((i + 1) * per, self.mask.len());
                let mask = &self.mask[start .. end];

                let mut parts = Vec::new();
                for &m in mask.iter() {
                    assert!(m >= 0);
                    if m >= original_count as i32 {
                        let idx = m as usize - original_count;
                        let part = (right.0[self.ty.split_part(idx)].clone(),
                                    self.ty.part_index(idx));
                        parts.push(part);
                    } else {
                        let part = (left.0[self.ty.split_part(m as usize)].clone(),
                                    self.ty.part_index(m as usize));
                        parts.push(part);
                    }
                }

                let mut parts_it = parts.iter().peekable();

                let mut left = None;
                let mut right = None;
                let mut new_mask = Vec::new();
                loop {
                    let &&(ref value, idx) = if let Some(p) = parts_it.peek() {
                        p
                    } else {
                        break;
                    };

                    if left.is_none() {
                        left = Some(value.clone());
                    } else if right.is_none() {
                        if left.as_ref() != Some(&value) {
                            right = Some(value.clone());
                        }
                    } else if right.as_ref() != Some(&value) &&
                        left.as_ref() != Some(&value)
                    {
                        // %shuffle = shufflevector <8 x i32> %left, <8 x i32> %right, <4 x i32> <i32 0, i32 4, i32 8, i32 12>
                        // =>
                        // %shuffle1 = shufflevector <4 x i32> %left1, <4 x i32> %left2, <4 x i32> <i32 0, i32 4, i32 4, i32 4>
                        // %shuffle2 = shufflevector <4 x i32> %shuffle1, <4 x i32> %right1, <4 x i32> <i32 0, i32 1, i32 4, i32 4>
                        // %shuffle3 = shufflevector <4 x i32> %shuffle2, <4 x i32> %right2, <4 x i32> <i32 0, i32 1, i32 2, i32 7>

                        let mask_len = new_mask.len();
                        while new_mask.len() < per {
                            let &v: &i32 = new_mask.last().unwrap();
                            new_mask.push(v);
                        }

                        let intermediate_shuffle = Shuffle {
                            ty: legal_ty,
                            mask: new_mask.clone(),
                        };

                        new_mask.clear();
                        for i in (0..mask_len) {
                            new_mask.push(i as i32);
                        }

                        intermediate_shuffle.emit(o, n.get(), left.unwrap(),
                                                  right.unwrap(), MODE);
                        left = Some(Value::Named(n.last()));
                        right = None;
                        continue;
                    }

                    parts_it.next();

                    let is_left = left.as_ref() == Some(&value);
                    let is_right = right.as_ref() == Some(&value);

                    assert!(is_left != is_right);

                    let offset;
                    if is_left {
                        offset = 0;
                    } else {
                        offset = per;
                    }

                    new_mask.push((idx + offset) as i32);
                }

                while new_mask.len() < per {
                    let &v: &i32 = new_mask.last().unwrap();
                    new_mask.push(v);
                }
                shuffle.mask = new_mask;

                let mut bypass = right.is_none() || right.as_ref() == Some(&undef);
                let mut i = 0;
                let rem = self.ty.rem_last_split();
                loop {
                    if !bypass || i == shuffle.mask.len() { break; }

                    let expected;
                    if rem != 0 && i > rem - 1 {
                        expected = rem - 1;
                    } else {
                        expected = i;
                    }

                    bypass = expected == shuffle.mask[i] as usize;

                    i += 1;
                }
                if bypass {
                    let l = match left.take() {
                        Some(Value::Named(name)) => Value::Named(name),
                        _ => unreachable!(),
                    };
                    out.push(l);
                } else {
                    let name = n.get();
                    shuffle.emit(o, name,
                                 left.unwrap(),
                                 right.unwrap_or_else(|| undef.clone() ),
                                 MODE);


                    out.push(Value::Named(name));
                }
            }

            LegalizedValue::new(out)
        }

        /*fn is_identity(&self) -> bool {
            for (i, &m) in self.mask.iter().enumerate() {
                if i as i32 != m {
                    return false;
                }
            }

            true
        }*/
    }

    pub fn main() {
        let out = open_ll("vector-canonicalization-shuffles.ll",
                          "Auto-generated tests for shuffle operations.");

        let seed: &[_] = &[1, 2, 3, 4]; // so we always generate the same sequence of shuffle masks.
        let mut rng: StdRng = SeedableRng::from_seed(seed);

        let fun_namer = InstName::new();
        fn shuffle<T: Write>(o: &mut T, name: Name, rng: &mut StdRng,
                             operand_ty: VectorType, ret_ty: VectorType) {
            /*assert!(tys.len() >= 1);

            let mut inner_ty = None;
            for (i, ty) in tys.iter().enumerate() {
                if inner_ty.is_none() {
                    inner_ty = Some(ty.inner);
                } else {
                    assert!(ty.inner == inner_ty.unwrap(), "{}", i);
                }
            }*/

            let name = format!("shuffle_{}_to_{}_{}",
                               operand_ty.legal_name(),
                               ret_ty.legal_name(),
                               name);
            count_test("shufflevector", &name[..]);

            let n = InstName::new();
            let mut state = StartingState::new_defining();

            //write_fn_start(&mut *o, &name[..], tys[tys.len() - 1],
            //               &tys[0..1], &n, &mut state);
            write_fn_start(&mut *o, &name[..], ret_ty,
                           &[operand_ty, operand_ty],
                           &n, &mut state);

            let (left, right) = match state {
                StartingState::Defining {
                    arg_names
                } => {
                    (arg_names[0], arg_names[1])
                },
                _ => unreachable!(),
            };

            let mut mask: Vec<i32> = Vec::new();
            for _ in (0..ret_ty.count()) {
                mask.push(rng.gen_range(0, (operand_ty.count() * 2 - 1) as i32));
            }

            let shuffle = Shuffle::new(operand_ty, mask);

            shuffle.emit(&mut *o, n.get(), Value::Named(left),
                         Value::Named(right),
                         Mode::Defining);

            write_fn_finish(&mut *o, ret_ty, FinishingState::new_defining(n.last()));

            let mut state = StartingState::new_checking();

            write_fn_start(&mut *o, &name[..], ret_ty,
                           &[operand_ty, operand_ty], &n,
                           &mut state);

            let (rets, args) = match state {
                StartingState::Checking {
                    ret_names: rets,
                    arg_names,
                } => {
                    assert_eq!(arg_names.len(), 2);
                    (rets, arg_names)
                },
                _ => unreachable!(),
            };

            let args: Vec<LegalizedValue> = args.into_iter()
                .map(|n| {
                    let v = n.into_iter()
                        .map(|n| Value::Named(n) )
                        .collect();
                    LegalizedValue::new(v)
                })
                .collect();

            let legalized_shuffle = shuffle.emit_checking(&mut *o,
                                                          args[0].clone(),
                                                          args[1].clone(),
                                                          &n);

            write_fn_finish(&mut *o, ret_ty, FinishingState::Checking {
                ret_names: {
                    let r = legalized_shuffle
                        .0
                        .into_iter()
                        .map(|v| {
                            match v {
                                Value::Named(name) => name,
                                _ => unreachable!(),
                            }
                        })
                        .collect();
                    r
                },
                ret_arg_names: rets,
            });
            writeln!(o, "").unwrap();
        }

        for &operand_count in super::VECTOR_COUNTS.iter() {
            for &ret_count in super::VECTOR_COUNTS.iter() {
                fun_namer.reset();
                for _ in (0..10) {
                    let mut o = out.borrow_mut();
                    // TODO: this generates redundant masks on smaller vector sizes.
                    shuffle(&mut *o, fun_namer.get(), &mut rng,
                            vector_type!(operand_count, super::I32Ty),
                            vector_type!(ret_count, super::I32Ty));
                }
            }
        }

    }
}

pub fn main() {
    let out = open_ll("vector-canonicalization-casts.ll",
                      "Auto-generated tests for all casts.");

    let cast = |op, from_ty: VectorType, to_ty: VectorType, impl_method| {
        assert_eq!(from_ty.count(), to_ty.count());

        let mut o = out.borrow_mut();
        //let mut o = ::std::io::stdout();
        let n = InstName::new();

        let name = format!("{}_cast_{}_to_{}",
                           op, from_ty.legal_name(), to_ty.legal_name());
        count_test("cast", &name[..]);

        let from_llty = from_ty.llvm_type_str();
        let to_llty = to_ty.llvm_type_str();

        let mut state = StartingState::new_defining();

        write_fn_start(&mut *o, &name[..], to_ty, &[from_ty], &n,
                       &mut state);

        let input = match state {
            StartingState::Defining {
                arg_names
            } => {
                arg_names[0]
            },
            _ => unreachable!(),
        };

        writeln!(o, "  %{inst_name} = {op} {fty} %{ip} to {tty}",
                 ip=input, inst_name=n.get(), op=op, fty=from_llty, tty=to_llty).unwrap();

        write_fn_finish(&mut *o, to_ty, FinishingState::new_defining(n.last()));

        // now emit the CHECK-* stuff:
        let mut state = StartingState::new_checking();

        write_fn_start(&mut *o, &name[..], to_ty, &[from_ty], &n,
                       &mut state);

        let (rets, arg_names) = match state {
            StartingState::Checking {
                ret_names: rets,
                arg_names,
            } => (rets, arg_names),
            _ => unreachable!(),
        };

        let (to_split_count, legal_toty) = to_ty.legalized_type();
        let (from_split_count, legal_fromty) = from_ty.legalized_type();

        let legal_tollty = legal_toty.llvm_type_str();
        let legal_fromllty = legal_fromty.llvm_type_str();

        let mut parts = Vec::new();
        match impl_method {
            ImplMethod::Scalar => {
                let to_elem_llty = legal_toty.inner.llvm_type_str();
                let from_elem_llty = legal_fromty.inner.llvm_type_str();

                let mut last = None;
                for i in (0..from_ty.count()) {
                    let idx = from_ty.part_index(i);

                    let extracted_name = n.get();
                    let casted_name = n.get();
                    let dest_src = if to_ty.part_index(i) == 0 {
                        if let Some(last) = last {
                            parts.push(last);
                        }
                        "undef".to_string()
                    } else {
                        format!("%{}", last.unwrap())
                    };
                    let inserted_name = n.get();

                    let source_name = arg_names[0][from_ty.split_part(i)];

                    writeln!(o, "; CHECK-NEXT:    %{name} = extractelement {fty} %{last_name}, i32 {idx}",
                             name=extracted_name, fty=legal_fromllty, last_name=source_name, idx=idx).unwrap();
                    writeln!(o, "; CHECK-NEXT:    %{name} = {op} {fty} %{last_name} to {tty}",
                             name=casted_name, tty=to_elem_llty, fty=from_elem_llty,
                             last_name=extracted_name, op=op).unwrap();
                    writeln!(o, "; CHECK-NEXT:    %{name} = insertelement {tty} {dest_src}, {scalar_ty} %{last_name}, i32 {idx}",
                             name=inserted_name, dest_src=dest_src, tty=legal_tollty,
                             last_name=casted_name, idx=to_ty.part_index(i),
                             scalar_ty=legal_toty.inner.llvm_type_str()).unwrap();

                    last = Some(n.last());
                }

                if let Some(last) = last {
                    parts.push(last);
                }
            },
            ImplMethod::Vector => {
                assert_eq!(from_split_count, to_split_count);
                for i in (0..to_split_count) {
                    let part = n.get();
                    writeln!(o, "; CHECK-NEXT:    %{name} = {op} {fty} %{last_name} to {tty}",
                             name=part, tty=legal_tollty, fty=legal_fromllty,
                             last_name=arg_names[0][i], op=op).unwrap();
                    parts.push(part);
                }
            },
        }

        let state = FinishingState::Checking {
            ret_names: parts,
            ret_arg_names: rets,
        };
        write_fn_finish(&mut *o, to_ty, state);
        writeln!(o, "").unwrap();
    };
    // |name, op, from_type, to_type, size, impl_method|

    let counts = VECTOR_COUNTS;

    let fp_int_casts = |count| {
        let floatxty = vector_type!(count, F32Ty);
        let doublexty = vector_type!(count, F64Ty);
        let i8xty = vector_type!(count, I8Ty);
        let i16xty = vector_type!(count, I16Ty);
        let i32xty = vector_type!(count, I32Ty);
        let i64xty = vector_type!(count, I64Ty);

        let floats = [floatxty, doublexty];
        let integers = [i8xty, i16xty, i32xty, i64xty];

        fn method(left: VectorType, right: VectorType) -> ImplMethod {
            if left.inner.size() == right.inner.size() {
                ImplMethod::Vector
            } else {
                ImplMethod::Scalar
            }
        }

        for &fty in floats.iter() {
            for &tty in integers.iter() {
                cast("fptoui", fty, tty, method(fty, tty));
            }
        }
        for &fty in floats.iter() {
            for &tty in integers.iter() {
                cast("fptosi", fty, tty, method(fty, tty));
            }
        }
        for &fty in floats.iter() {
            for &tty in integers.iter() {
                cast("uitofp", tty, fty, method(tty, fty));
            }
        }
        for &fty in floats.iter() {
            for &tty in integers.iter() {
                cast("sitofp", tty, fty, method(tty, fty));
            }
        }
    };
    for &count in counts.iter() {
        fp_int_casts(count);
    }

    let other_casts = |count| {
        let i8ptrty = vector_type!(count, I8PtrTy);
        let i32ty = vector_type!(count, I32Ty);
        let i64ty = vector_type!(count, I64Ty);
        let fty = vector_type!(count, F32Ty);
        let dty = vector_type!(count, F64Ty);

        cast("ptrtoint", i8ptrty, i32ty, ImplMethod::Vector);
        cast("inttoptr", i32ty, i8ptrty, ImplMethod::Vector);

        let four = [i32ty, fty];
        for &left in four.iter() {
            for &right in four.iter() {
                if left != right {
                    cast("bitcast", left, right, ImplMethod::Vector);
                }
            }
        }

        let eight = [i64ty, dty];
        for &left in eight.iter() {
            for &right in eight.iter() {
                if left != right {
                    cast("bitcast", left, right, ImplMethod::Vector);
                }
            }
        }
    };
    for &count in counts.iter() {
        other_casts(count);
    }

    for &count in counts.iter() {
        let i8ty = vector_type!(count, I8Ty);
        let i16ty = vector_type!(count, I16Ty);
        let i32ty = vector_type!(count, I32Ty);
        let i64ty = vector_type!(count, I64Ty);

        let m = ImplMethod::Scalar;

        cast("zext", i8ty, i16ty, m);
        cast("zext", i8ty, i32ty, m);
        cast("zext", i8ty, i64ty, m);
        cast("zext", i16ty, i32ty, m);
        cast("zext", i16ty, i64ty, m);
        cast("zext", i32ty, i64ty, m);

        cast("sext", i8ty, i16ty, m);
        cast("sext", i8ty, i32ty, m);
        cast("sext", i8ty, i64ty, m);
        cast("sext", i16ty, i32ty, m);
        cast("sext", i16ty, i64ty, m);
        cast("sext", i32ty, i64ty, m);

        cast("trunc", i64ty, i32ty, m);
        cast("trunc", i64ty, i16ty, m);
        cast("trunc", i64ty, i8ty, m);
        cast("trunc", i32ty, i16ty, m);
        cast("trunc", i32ty, i8ty, m);
        cast("trunc", i16ty, i8ty, m);
    }


    let out = open_ll("vector-canonicalization-binops.ll",
                      "Auto-generated tests for all binary operations.");

    let binop = |op, ty: VectorType, attrs: &str| {
        let mut o = out.borrow_mut();

        let name = format!("{}_binop_{}{}", op, ty.legal_name(),
                           if attrs != "" {
                               let nice_attrs = attrs.replace(" ", "_");
                               format!("_{}", &nice_attrs[..nice_attrs.len() - 1])
                           } else { "".to_string() });
        count_test("binop", &name[..]);

        let n = InstName::new();

        let mut state = StartingState::new_defining();

        write_fn_start(&mut *o, &name[..], ty, &[ty, ty], &n,
                       &mut state);

        let (input1, input2) = match state {
            StartingState::Defining { arg_names } => {
                (arg_names[0], arg_names[1])
            },
            _ => unreachable!(),
        };

        writeln!(o, "  %{inst_name} = {op} {attrs}{ty} %{i1}, %{i2}",
                 i1=input1, i2=input2, inst_name=n.get(), op=op,
                 ty=ty.llvm_type_str(), attrs=attrs).unwrap();

        write_fn_finish(&mut *o, ty, FinishingState::new_defining(n.last()));

        let mut state = StartingState::new_checking();

        write_fn_start(&mut *o, &name[..], ty, &[ty, ty], &n,
                       &mut state);

        let (rets, args) = match state {
            StartingState::Checking {
                ret_names: rets,
                arg_names,
            } => (rets, arg_names),
            _ => unreachable!(),
        };

        let mut parts = Vec::new();

        let (split_count, legal_ty) = ty.legalized_type();
        let legal_llty = legal_ty.llvm_type_str();
        for i in (0..split_count) {
            let part = n.get();
            writeln!(o, "; CHECK-NEXT:    %{name} = {op} {attrs}{ty} %{lhs}, %{rhs}",
                     name=part, ty=legal_llty, lhs=args[0][i], rhs=args[1][i],
                     op=op, attrs=attrs).unwrap();
            parts.push(part);
        }

        write_fn_finish(&mut *o, ty, FinishingState::Checking {
            ret_names: parts,
            ret_arg_names: rets,
        });
        writeln!(o, "").unwrap();
    };

    #[allow(non_upper_case_globals)]
    const iattrs: &'static [&'static str] = &["nuw ", "nsw ", "nuw nsw "];
    #[allow(non_upper_case_globals)]
    const iops: &'static [&'static str] = &["add", "sub", "mul", "shl"];
    #[allow(non_upper_case_globals)]
    const iusops: &'static [&'static str] = &["udiv", "sdiv", "lshr", "ashr"];

    #[allow(non_upper_case_globals)]
    const bitwise_ops: &'static [&'static str] = &["and", "xor", "or", "urem", "srem"];

    #[allow(non_upper_case_globals)]
    const fops: &'static [&'static str] = &["fadd", "fsub", "fmul", "fdiv", "frem"];

    for &count in counts.iter() {
        let fty = vector_type!(count, F32Ty);
        let dty = vector_type!(count, F64Ty);

        for &op in fops.iter() {
            binop(op, fty, "");
            binop(op, fty, "fast ");
            binop(op, dty, "");
            binop(op, dty, "fast ");
        }
    }

    for &count in counts.iter() {
        let tys = [vector_type!(count, I8Ty),
                   vector_type!(count, I16Ty),
                   vector_type!(count, I32Ty),
                   vector_type!(count, I64Ty)];

        for &ty in tys.iter() {
            for op in iops.iter() {
                for attr in iattrs.iter() {
                    binop(op, ty, attr);
                }
            }

            for op in iusops.iter() {
                binop(op, ty, "");
                binop(op, ty, "exact ");
            }

            for op in bitwise_ops.iter() {
                binop(op, ty, "");
            }
        }
    }

    shuffle_tests::main();
    call_tests::main();
    cmp_tests::main();
    extract_tests::main();
    insert_tests::main();
    store_tests::main();
    load_tests::main();
    phi_tests::main();

    finished_generating_tests();
}
