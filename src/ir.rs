/// trying, yet again, to strike the right balance between programmability
/// and amount of effort.

use std;
use std::cell::{RefCell, Cell};
use std::fmt;
use std::io::Write;
use std::rc::Rc;

use super::{Ty, InstName, Mode, TypeTrait, FunctionType,
            VectorType};

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Attrs {
    pub non_null: bool,
    pub no_capture: bool,
    pub dereferenceable: Option<usize>,
    pub align: Option<usize>,
}
impl Default for Attrs {
    fn default() -> Attrs {
        Attrs {
            non_null: false,
            no_capture: false,
            dereferenceable: None,
            align: None,
        }
    }
}
impl Attrs {
    pub fn new_split() -> Attrs {
        Attrs {
            no_capture: true,
            non_null: true,
            dereferenceable: Some(16),
            .. Default::default()
        }
    }
    pub fn emit<T: Write>(&self, o: &mut T, mut first: bool) -> bool {
        if self.no_capture {
            write!(o, "{}nocapture",
                   if !first {
                       " "
                   } else {
                       ""
                   }).unwrap();
            first = false;
        }

        if self.non_null {
            write!(o, "{}nonnull",
                   if !first {
                       " "
                   } else {
                       ""
                   }).unwrap();
            first = false;
        }

        if let Some(d) = self.dereferenceable {
            write!(o, "{}dereferenceable({})",
                   if !first {
                       " "
                   } else {
                       ""
                   },
                   d).unwrap();
            first = false;
        }

        first
    }

    pub fn fmt_into(&self, str: &mut String) -> bool {
        let mut first = true;
        if self.no_capture {
            str.push_str("nocapture");
            first = false;
        }

        if self.non_null {
            if !first { str.push_str(" "); }

            str.push_str("nonnull");
        }

        if let Some(d) = self.dereferenceable {
            if !first { str.push_str(" "); }

            str.push_str(&format!("dereferenceable({})", d)[..]);
        }

        !first
    }
}

//pub struct Module {

//}

pub struct Fun {
    name: String,

    ret_ty: Option<Ty>,
    arg_tys: Vec<Ty>,

    args: Vec<Value>,

    arg_attrs: Vec<Attrs>,

    blocks: Vec<BB>,
}

impl Fun {
    pub fn new(name: String) -> Fun {
        assert!(name.starts_with('@'));
        Fun {
            name: name,

            ret_ty: None,
            arg_tys: Vec::new(),

            args: Vec::new(),

            arg_attrs: Vec::new(),

            blocks: Default::default(),
        }
    }
    pub fn new_with_ty(name: String, FunctionType { ret, args }: FunctionType) -> Fun {
        let arg_count = args.len();
        let mut f = Fun {
            name: name,

            ret_ty: ret,
            arg_tys: args,

            args: Vec::new(),

            arg_attrs: Vec::new(),

            blocks: Default::default(),
        };

        let mut args = Vec::with_capacity(arg_count);
        let mut arg_attrs = Vec::with_capacity(arg_count);

        for (i, arg_ty) in f.arg_tys.iter().enumerate() {
            let arg_v = Val::new_named(arg_ty.clone(), i);

            args.push(arg_v);
            arg_attrs.push(Default::default());
        }

        f.args = args;
        f.arg_attrs = arg_attrs;

        f
    }

    pub fn arg_value(&self, arg: usize) -> Value {
        self.args[arg].clone()
    }
    pub fn args(&self) -> usize { self.args.len() }

    pub fn name(&self) -> &str { &self.name[..] }

    pub fn add_arg(&mut self, ty: Ty, attr: Option<Attrs>) -> Value {
        assert_eq!(self.args.len(), self.arg_tys.len());
        let arg_v = Val::new_named(ty.clone(), self.args.len());
        self.arg_tys.push(ty);
        self.args.push(arg_v.clone());
        self.arg_attrs.push(attr.unwrap_or_default());
        arg_v
    }

    pub fn add_inst(&mut self, inst: Instruction) -> Option<Value> {
        if self.blocks.len() == 0 {
            let bb = BB::new("entry");
            self.blocks.push(bb);
        }

        let bb = self.blocks.last_mut().unwrap();
        bb.add_inst(inst)
    }
    pub fn insert_inst_before(&mut self, before: &Instruction,
                              inst: Instruction) -> Option<Value> {
        let bb = self.blocks.last_mut().unwrap();
        bb.insert_before(before, inst)
    }

    pub fn set_ret_ty(&mut self, ty: Ty) {
        self.ret_ty = Some(ty);
    }

    pub fn new_block<T: std::string::ToString>(&mut self, name: T) -> BB {
        let bb = BB::new(name);
        self.blocks.push(bb.clone());
        bb
    }

    pub fn declare<T: Write>(&self, o: &mut T) {
        write!(o, "declare {} {}(", self.ret_ty.llvm_type_str(), self.name)
            .unwrap();
        for i in (0..self.args.len()) {
            if i != 0 {
                write!(o, ", ")
                    .unwrap();
            }

            write!(o, "{}", self.arg_tys[i].llvm_type_str()).unwrap();
            self.arg_attrs[i].emit(o, false);
        }

        writeln!(o, ")")
            .unwrap();
    }

    pub fn emit<T: Write>(&self, o: &mut T, mode: Mode) {
        assert_eq!(self.args.len(), self.arg_tys.len());
        let n = InstName::new();
        n.reset_to(self.args.len());

        // give all instructions a name:
        for b in self.blocks.iter() {
            b.assign_names(&n);
        }

        mode.emit_label_prefix(o);
        write!(o, "define {} {}(", self.ret_ty.llvm_type_str(), self.name)
            .unwrap();
        for i in (0..self.args.len()) {
            if i != 0 {
                write!(o, ", ")
                    .unwrap();
            }

            write!(o, "{}", self.arg_tys[i].llvm_type_str()).unwrap();
            self.arg_attrs[i].emit(o, false);
        }

        writeln!(o, ") {{")
            .unwrap();

        for (i, b) in self.blocks.iter().enumerate() {
            if i != 0 {
                //writeln!(o, "").unwrap();
            }
            b.emit(o, mode);
        }

        match mode {
            Mode::Defining => {
                writeln!(o, "}}")
                    .unwrap();
            },
            Mode::Checking => {
                writeln!(o, "; CHECK-NEXT:  }}")
                    .unwrap();
            },
        }
    }

    pub fn build_type(&self) -> Ty {
        let fty = FunctionType {
            ret: self.ret_ty.clone(),
            args: self.arg_tys.clone(),
        };
        let fty = Ty::Function(Rc::new(fty));

        fty.get_pointer_to()
    }

    pub fn build_value(&self) -> Value {
        Val::new_const(self.build_type(), self.name.clone())
    }


    pub fn add_ret_split_store(&mut self, value: Value, part: usize) {
        assert!(part != 0);
        let ptr = self.args[part - 1].clone();
        let i = Inst::new_store(value, ptr, Some(16));
        self.add_inst(i);
    }
    pub fn create_split_ret_stores(&mut self, vals: &[Value]) {
        assert!(vals.len() >= 1);
        for i in (1..vals.len()) {
            self.add_ret_split_store(vals[i].clone(), i);
        }
        let r = Inst::new_ret(vals[0].clone());
        self.add_inst(r);
    }
}

/*impl Drop for Fun {
fn drop(&mut self) {
// clean up possible circler references:
for i in (0..self.insts.0.len()) {
self.insts.0[i].operands.clear();
            }
        }
    }*/

#[derive(Clone)]
pub struct BasicBlock {
    name: String,
    insts: Insts,
}

#[derive(Clone)]
pub struct BB(pub Rc<RefCell<BasicBlock>>);

impl BB {
    pub fn new<T: std::string::ToString>(name: T) -> BB {
        let bb = BasicBlock {
            name: name.to_string(),
            insts: Default::default(),
        };

        BB(Rc::new(RefCell::new(bb)))
    }
    pub fn name(&self) -> String {
        self.0.borrow().name.clone()
    }
    pub fn add_inst(&self, i: Instruction) -> Option<Value> {
        let mut bm = self.0.borrow_mut();
        let r = if i.has_result() {
            Some(i.get_value())
        } else {
            None
        };

        bm.insts.push(i);

        r
    }
    pub fn insert_before(&self, before: &Instruction,
                         inst: Instruction) -> Option<Value> {
        let mut bm = self.0.borrow_mut();

        let r = if inst.has_result() {
            Some(inst.get_value())
        } else {
            None
        };

        bm.insts.insert_before(before, inst);

        r
    }

    fn assign_names(&self, n: &InstName) {
        let b = self.0.borrow();
        for inst in b.insts.0.iter() {
            match inst.get_value_opt() {
                Some(ref value) if value.name_pending() => {
                    value.set_name(n.get());
                },
                _ => {},
            }
        }
    }

    fn emit<T: Write>(&self, o: &mut T, mode: Mode) {
        let b = self.0.borrow();

        mode.emit_bb_prefix(o);
        writeln!(o, "{}:", b.name).unwrap();

        for inst in b.insts.0.iter() {
            inst.emit(o, mode);
        }
    }
}

#[derive(Clone)]
pub struct Insts(pub Vec<Instruction>);
impl Default for Insts {
    fn default() -> Insts {
        Insts(Vec::new())
    }
}
impl Insts {
    pub fn push(&mut self, i: Instruction) {
        self.0.push(i);
    }
    pub fn insert_before(&mut self, before: &Instruction, i: Instruction) {
        let id = before.id();
        for idx in (0..self.0.len()) {
            if self.0[idx].id() == id {
                self.0.insert(idx, i);
                return;
            }
        }

        unreachable!();
    }
}


#[derive(Eq, PartialEq, Clone, Debug)]
pub enum V {
    Named(Ty, Option<super::Name>),
    Constant(Ty, String),
    ConstantExpr {
        ty: Ty,

        ir: String,
        operands: Vec<Value>,
    },
}
impl V {
    pub fn str_with_type(&self) -> Option<String> {
        match self {
            &V::Named(ref ty, name) => {
                name
                    .map(|n| {
                        format!("{} %{}", ty.llvm_type_str(), n)
                    })
            },
            &V::Constant(ref ty, ref v) => {
                Some(format!("{} {}", ty.llvm_type_str(), v))
            },
            &V::ConstantExpr { ref ty, .. } => {
                Some(format!("{} {}", ty.llvm_type_str(),
                             self.str_without_type().unwrap()))
            },
        }
    }
    pub fn str_without_type(&self) -> Option<String> {
        match self {
            &V::Named(_, name) => {
                name
                    .map(|n| {
                        format!("%{}", n)
                    })
            },
            &V::Constant(_, ref v) => {
                Some(format!("{}", v))
            },
            &V::ConstantExpr {
                ref ir, ref operands,
                ..
            } => {
                assert!(operands.iter().all(|o| {
                    let b = o.0.borrow();
                    match &*b {
                        &V::Constant(..) | &V::ConstantExpr { .. } => true,
                        _ => false,
                    }
                }));

                let mut opit = operands.iter();

                let with_type = Cell::new(false);

                let mut fmtit = ir.split(|c| {
                    if c == '?' {
                        with_type.set(false);
                        true
                    } else if c == ';' {
                        with_type.set(true);
                        true
                    } else {
                        false
                    }
                }).peekable();

                let mut ir_out = "".to_string();

                loop {
                    let op_opt = opit.next();
                    let fmt_opt = fmtit.next();

                    assert!((op_opt.is_some() && fmt_opt.is_some()) ||
                            (op_opt.is_none() && fmtit.peek().is_none()));

                    let prefix = fmt_opt.unwrap();
                    ir_out.push_str(prefix);

                    if op_opt.is_none() {
                        break;
                    }

                    let operand = op_opt.unwrap();
                    let operand_str = if with_type.get() {
                        operand.str_with_type()
                    } else {
                        operand.str_without_type()
                    };
                    ir_out.push_str(&operand_str[..]);
                }

                Some(ir_out)
            },
        }
    }
}
impl ::std::fmt::Display for V {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            &V::Named(ref ty, name) => {
                write!(f, "{} %{}", ty.llvm_type_str(),
                       name.unwrap_or(0))
            },
            &V::Constant(ref ty, ref v) => {
                write!(f, "{} {}", ty.llvm_type_str(), v)
            },
            &V::ConstantExpr { .. } => {
                write!(f, "{}", self.str_with_type().unwrap())
            },
        }
    }
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Val(RefCell<V>);
pub type Value = Rc<Val>;
impl Val {
    pub fn new_name_pending(ty: Ty) -> Value {
        let v = Val(RefCell::new(V::Named(ty, None)));
        Rc::new(v)
    }
    pub fn new_named(ty: Ty, name: super::Name) -> Value {
        let v = Val(RefCell::new(V::Named(ty, Some(name))));
        Rc::new(v)
    }
    pub fn new_const(ty: Ty, v: String) -> Value {
        let v = Val(RefCell::new(V::Constant(ty, v)));
        Rc::new(v)
    }

    pub fn new_const_bitcast(from: Value, to: Ty) -> Value {
        let v = V::ConstantExpr {
            ir: format!("bitcast (; to {})", to.llvm_type_str()),
            operands: vec!(from),

            ty: to,
        };
        Rc::new(Val(RefCell::new(v)))
    }

    pub fn new_undef(ty: Ty) -> Value {
        let v = V::Constant(ty, "undef".to_string());
        Rc::new(Val(RefCell::new(v)))
    }

    pub fn new_const_i32(v: i32) -> Value {
        let v = V::Constant(super::I32Ty.into(), format!("{}", v));
        Rc::new(Val(RefCell::new(v)))
    }
    pub fn new_const_true() -> Value {
        let v = V::Constant(super::I1Ty.into(), "true".to_string());
        Rc::new(Val(RefCell::new(v)))
    }
    pub fn new_const_false() -> Value {
        let v = V::Constant(super::I1Ty.into(), "false".to_string());
        Rc::new(Val(RefCell::new(v)))
    }


    pub fn ty(&self) -> Ty {
        let b = self.0.borrow();
        match &*b {
            &V::Named(ref ty, _) |
            &V::Constant(ref ty, _) |
            &V::ConstantExpr { ref ty, .. } => ty.clone(),
        }
    }

    pub fn name_pending(&self) -> bool {
        !self.is_set()
    }

    fn is_set(&self) -> bool {
        let b = self.0.borrow();
        match &*b {
            &V::Named(_, None) => false,
            _ => true,
        }
    }
    pub fn set_name(&self, name: super::Name) {
        assert!(!self.is_set(), "value is already set!");

        let mut bm = self.0.borrow_mut();
        match &mut *bm {
            &mut V::Named(_, ref mut n) => {
                *n = Some(name);
            },
            _ => unreachable!(),
        }
    }
    pub fn str_with_type(&self) -> String {
        assert!(self.is_set());
        let b = self.0.borrow();
        b.str_with_type().unwrap()
    }
    pub fn str_without_type(&self) -> String {
        assert!(self.is_set());
        let b = self.0.borrow();
        b.str_without_type().unwrap()
    }
}

fn next_id() -> u64 {
    thread_local!(static NEXT: Cell<u64> = Cell::new(0));
    NEXT.with(|next| {
        let id = next.get();
        next.set(id + 1);
        id
    })
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Hash, Copy, Clone)]
pub enum Signess {
    Unsigned,
    Signed,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Hash, Copy, Clone)]
pub enum IntPred {
    Eq, Neq,
    Gt(Signess), Ge(Signess),
    Lt(Signess), Le(Signess),
}
impl fmt::Display for IntPred {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::IntPred::*;
        use self::Signess::*;

        let s = match self {
            &Eq => "eq",
            &Neq => "ne",

            &Gt(Signed) => "sgt",
            &Gt(Unsigned) => "ugt",
            &Ge(Signed) => "sge",
            &Ge(Unsigned) => "uge",

            &Lt(Signed) => "slt",
            &Lt(Unsigned) => "ult",
            &Le(Signed) => "sle",
            &Le(Unsigned) => "ule",
        };
        write!(f, "{}", s)
    }
}
impl IntPred {
    pub fn permutations() -> &'static [IntPred] {
        use self::IntPred::*;
        use self::Signess::*;

        const T: &'static [IntPred] =
            &[
                Eq, Neq,

                Gt(Signed), Gt(Unsigned),
                Ge(Signed), Ge(Unsigned),

                Lt(Signed), Lt(Unsigned),
                Le(Signed), Le(Unsigned),
                ];
        T
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Hash, Copy, Clone)]
pub enum Ordering {
    Ordered,
    Unordered,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Hash, Copy, Clone)]
pub enum FpPred {
    True, False,

    Eq(Ordering), Neq(Ordering),
    Gt(Ordering), Ge(Ordering),

    Nan(Ordering),
}
impl fmt::Display for FpPred {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::FpPred::*;
        let s = match self {
            &True => "true",
            &False => "false",

            &Eq(Ordering::Ordered) => "oeq",
            &Eq(Ordering::Unordered) => "ueq",
            &Neq(Ordering::Ordered) => "one",
            &Neq(Ordering::Unordered) => "une",

            &Gt(Ordering::Ordered) => "ogt",
            &Gt(Ordering::Unordered) => "ugt",
            &Ge(Ordering::Ordered) => "oge",
            &Ge(Ordering::Unordered) => "uge",

            &Nan(Ordering::Ordered) => "ord",
            &Nan(Ordering::Unordered) => "uno",
        };
        write!(f, "{}", s)
    }
}
impl FpPred {
    pub fn permutations() -> &'static [FpPred] {
        use self::FpPred::*;

        const T: &'static [FpPred] =
            &[
                True, False,
                Eq(Ordering::Ordered), Eq(Ordering::Unordered),
                Neq(Ordering::Ordered), Neq(Ordering::Unordered),

                Gt(Ordering::Ordered), Gt(Ordering::Unordered),
                Ge(Ordering::Ordered), Ge(Ordering::Unordered),

                Nan(Ordering::Ordered), Nan(Ordering::Unordered),
                ];
        T
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Hash, Copy, Clone)]
pub struct FastMathAttrs {
    fast: bool,
}
impl FastMathAttrs {
    pub fn permutations() -> &'static [FastMathAttrs] {
        const T: &'static [FastMathAttrs] =
            &[FastMathAttrs { fast: false },
              //FastMathAttrs { fast: true },
              ];

        T
    }
    pub fn fn_name_str(&self) -> &'static str {
        match self {
            &FastMathAttrs {
                fast: false,
            } => "",
            &FastMathAttrs {
                fast: true,
            } => "_fast",
        }
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Hash, Copy, Clone)]
pub enum Cmp {
    Fp(FpPred, FastMathAttrs),
    Int(IntPred),
}

pub struct Inst {
    id: u64,
    name: Option<Value>,

    ir: String,
    operands: Vec<Value>,
}
pub type Instruction = Rc<Inst>;
impl Inst {
    /// ';' is the operand type + name placement char, '?' places just the
    /// operand name without its type, and '|' places just the type (TODO).
    /// This format could be better if I felt like creating an actual parser.
    pub fn new(ty: Option<Ty>, ir: String, ops: Vec<Value>) -> Instruction {
        let i = Inst {
            id: next_id(),

            name: ty.map(|ty| {
                Val::new_name_pending(ty)
            }),

            ir: ir,
            operands: ops,
        };
        Rc::new(i)
    }

    pub fn new_load(from: Value, align: Option<usize>,
                    attrs: Option<&str>) -> Instruction {
        Inst::new_volatile_load(from, align, attrs, false)
    }
    pub fn new_volatile_load(from: Value, align: Option<usize>,
                             attrs: Option<&str>,
                             volatile: bool) -> Instruction {
        let elem_ty = match from.ty() {
            Ty::Pointer(elem) => (&*elem).clone(),
            _ => unreachable!(),
        };
        let ir = format!("load{} {}, ;{}{}",
                         if volatile { " volatile" }
                         else { "" }, elem_ty,
                         if let Some(a) = align {
                             format!(", align {}", a)
                         } else {
                             "".to_string()
                         },
                         if let Some(a) = attrs {
                             format!(", {}", a)
                         } else {
                             "".to_string()
                         });

        Inst::new(Some(elem_ty), ir, vec!(from))
    }
    pub fn new_store(value: Value, ptr: Value,
                     align: Option<usize>) -> Instruction {
        Inst::new_volatile_store(value, ptr, align, false)
    }
    pub fn new_volatile_store(value: Value, ptr: Value,
                              align: Option<usize>,
                              volatile: bool) -> Instruction {
        assert_eq!(Some(value.ty()), ptr.ty().get_pointer_element());
        let ir = format!("store{} ;, ;{}",
                         if volatile { " volatile" }
                         else { "" },
                         match align {
                             None => "".to_string(),
                             Some(a) => format!(", align {}", a),
                         });

        Inst::new(None, ir, vec!(value, ptr))
    }
    pub fn new_call(call: Value, args: &[Value], attrs: Option<&[Attrs]>) -> Instruction {
        let ret_ty = match call.ty().get_pointer_element() {
            Some(Ty::Function(fty)) => fty.ret.clone(),
            _ => unreachable!(),
        };

        if let Some(attrs) = attrs {
            assert_eq!(args.len(), attrs.len());
        }

        let mut ir = format!("call {} ?(", ret_ty.llvm_type_str());
        let mut operands = vec!(call);
        for (i, arg) in args.iter().enumerate() {
            ir.push_str(if i != 0 { ", " }
                        else { "" });
            ir.push_str(&format!("{}", arg.ty().llvm_type_str())[..]);
            ir.push_str(" ");

            if let Some(attrs) = attrs {
                if attrs[i].fmt_into(&mut ir) {
                    ir.push_str(" ");
                }
            }

            ir.push_str("?");

            operands.push(arg.clone());
        }
        ir.push_str(")");

        Inst::new(ret_ty, ir, operands)
    }
    pub fn new_alloca(ty: Ty, count: Option<usize>,
                      align: Option<usize>) -> Instruction {
        let ir = format!("alloca {}{}{}", ty.llvm_type_str(),
                         if let Some(c) = count {
                             format!(", i32 {}", c)
                         } else {
                             "".to_string()
                         },
                         if let Some(a) = align {
                             format!(", align {}", a)
                         } else {
                             "".to_string()
                         });

        Inst::new(Some(ty.get_pointer_to()), ir, vec!())
    }
    pub fn new_bitcast(from: Value, to: Ty) -> Instruction {
        let ir = format!("bitcast ; to {}", to.llvm_type_str());

        Inst::new(Some(to), ir, vec!(from))
    }
    pub fn new_ret(v: Value) -> Instruction {
        Inst::new(None, "ret ;".to_string(), vec!(v))
    }

    pub fn new_cmp(cmp: Cmp, left: Value, right: Value) -> Instruction {
        assert_eq!(left.ty(), right.ty());

        let result_ty: Ty = match left.ty() {
            Ty::Vector(VectorType { count, .. }) => {
                vector_type!(count, ::I1Ty).into()
            },
            _ => ::I1Ty.into(),
        };

        let ir = match cmp {
            Cmp::Fp(pred, FastMathAttrs { fast }) => {
                format!("fcmp {}{} ;, ?",
                        if fast { "fast " } else { "" },
                        pred)
            },
            Cmp::Int(pred) => {
                format!("icmp {} ;, ?", pred)
            },
        };

        Inst::new(Some(result_ty), ir, vec!(left, right))
    }
    pub fn new_select(b: Value, left: Value, right: Value) -> Instruction {
        let ir = "select ;, ;, ;".to_string();

        assert_eq!(left.ty(), right.ty());

        Inst::new(Some(left.ty()), ir, vec!(b, left, right))
    }

    pub fn new_extractelement(from: Value, idx: Value) -> Instruction {
        let inner = match from.ty() {
            Ty::Vector(ref v) => v.inner,
            _ => panic!("expected vector type"),
        };

        Inst::new(Some(inner.into()), "extractelement ;, ;".to_string(),
                  vec!(from, idx))
    }

    pub fn new_insertelement(from: Value, v: Value, idx: Value) -> Instruction {
        let from_ty = from.ty();
        let inner: Ty = match from_ty {
            Ty::Vector(ref v) => v.inner.into(),
            _ => panic!("expected vector type"),
        };

        assert_eq!(inner, v.ty());
        Inst::new(Some(from_ty),
                  "insertelement ;, ;, ;".to_string(),
                  vec!(from, v, idx))
    }
    pub fn new_binop(op: &'static str,
                     left: Value, right: Value) -> Instruction {
        assert_eq!(left.ty(), right.ty());

        Inst::new(Some(left.ty()),
                  format!("{} ;, ?", op),
                  vec!(left, right))
    }
    pub fn new_and(left: Value, right: Value) -> Instruction {
        Inst::new_binop("and", left, right)
    }
    pub fn new_xor(left: Value, right: Value) -> Instruction {
        Inst::new_binop("xor", left, right)
    }
    pub fn new_not(left: Value) -> Instruction {
        use super::LLVMType;
        match left.ty() {
            Ty::Scalar(LLVMType::I1) => {},
            _ => panic!("expected `i1`"),
        }

        Inst::new_xor(left, Val::new_const_true())
    }
    pub fn new_gep(ptr: Value, offsets: &[Value],
                   inbounds: bool) -> Instruction {
        let mut ty = ptr.ty();
        let inner_ty = match ty {
            Ty::Pointer(ref inner) => (&**inner).clone(),
            _ => {
                panic!("expected ptr operand");
            },
        };

        let mut offsets_ir = "".to_string();
        for _ in offsets.iter() {
            offsets_ir.push_str(", ;");
            match ty {
                Ty::Void => unreachable!(),
                Ty::Function(_) => {
                    panic!("unexpected function type in gep");
                },
                Ty::Scalar(_) => {
                    panic!("unexpected scalar type in gep");
                },
                Ty::Struct { .. } => unimplemented!(),
                Ty::Array(at) => {
                    ty = at.elem.clone();
                },
                Ty::Pointer(to) => {
                    ty = (&*to).clone();
                },
                Ty::Vector(vty) => {
                    ty = vty.inner.clone().into();
                },
            }
        }

        let ty_ptr = ty.get_pointer_to();
        let ir = format!("getelementptr{} {}, ;{}",
                         if inbounds { " inbounds" }
                         else { "" },
                         inner_ty.llvm_type_str(),
                         offsets_ir);
        let mut operands = vec!(ptr);
        operands.extend(offsets.iter().map(|o| o.clone() ));
        Inst::new(Some(ty_ptr),
                  ir, operands)
    }

    pub fn new_phi(ty: Ty, ops: Vec<(Value, BB)>) -> Instruction {
        assert!(ops.len() > 0);
        let mut new_ops = Vec::with_capacity(ops.len());
        let mut ir = format!("phi {}", ty.llvm_type_str());
        for (i, (v, b)) in ops.into_iter().enumerate() {
            let m = format!("{} [ ?, %{} ]",
                            if i != 0 { "," }
                            else { "" },
                            b.name());
            ir.push_str(&m[..]);

            new_ops.push(v);
        }

        Inst::new(Some(ty), ir, new_ops)
    }

    pub fn new_uncond_br(dest: &BB) -> Instruction {
        let ir = format!("br label %{}", dest.name());
        Inst::new(None, ir, vec!())
    }

    pub fn new_cond_br(cond: Value, on_true: &BB, on_false: &BB) -> Instruction {
        let ir = format!("br ;, label %{}, label %{}",
                         on_true.name(), on_false.name());
        Inst::new(None, ir, vec!(cond))
    }

    /// In general, this isn't safe.
    pub fn set_operand(&mut self, idx: usize, v: Value) {
        self.operands[idx] = v;
    }

    pub fn id(&self) -> u64 {
        self.id
    }

    pub fn has_result(&self) -> bool {
        self.name.is_some()
    }
    pub fn get_value(&self) -> Value {
        assert!(self.has_result());
        self.name.as_ref().unwrap().clone()
    }
    pub fn get_value_opt(&self) -> Option<Value> {
        self.name.clone()
    }

    pub fn get_operand(&self, i: usize) -> Value {
        self.operands[i].clone()
    }

    pub fn emit<T: Write>(&self, o: &mut T, mode: Mode) {
        let mut opit = self.operands.iter();

        let with_type = Cell::new(false);

        let mut fmtit = self.ir.split(|c| {
            if c == '?' {
                with_type.set(false);
                true
            } else if c == ';' {
                with_type.set(true);
                true
            } else {
                false
            }
        }).peekable();

        let mut ir_out = match self.name {
            Some(ref name) => {
                let b = name.0.borrow();
                format!("%{} = ", match &*b {
                    &V::Named(_, Some(name)) => name,
                    _ => unreachable!(),
                })
            },
            None => {
                "".to_string()
            },
        };

        loop {
            let op_opt = opit.next();
            let fmt_opt = fmtit.next();

            assert!((op_opt.is_some() && fmt_opt.is_some()) ||
                    (op_opt.is_none() && fmtit.peek().is_none()));

            let prefix = fmt_opt.unwrap();
            ir_out.push_str(prefix);

            if op_opt.is_none() {
                break;
            }

            let operand = op_opt.unwrap();
            let operand_str = if with_type.get() {
                operand.str_with_type()
            } else {
                operand.str_without_type()
            };
            ir_out.push_str(&operand_str[..]);
        }

        for line in ir_out.lines() {
            mode.emit_prefix(o);

            writeln!(o, "{}", line)
                .unwrap();
        }
    }
}
