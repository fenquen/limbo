use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::{storage::sqlite3_ondisk::DbHeader, Conn};

use super::{BranchOffset, CursorID, Insn, InsnReference, Program, Table};

/// 话术说明
/// pc -> insns的index
/// register -> registers的index
/// label -> pc
#[allow(dead_code)]
pub struct ProgramBuilder {
    nextFreeRegister: usize,
    nextFreeLabel: BranchOffset,
    nextFreeCursorId: usize,
    insns: Vec<Insn>,

    /// for temporarily storing instructions that will be put after Transaction opcode
    constant_insns: Vec<Insn>,

    /// 各个label对应的需要resolve的insn在insn列表的index列表
    unresolvedInsnIndexes: Vec<Vec<InsnReference>>,

    next_insn_label: Option<BranchOffset>,

    /// Cursors that are referenced by the program. vec的 index 是 cursor id
    pub tblNameTbls: Vec<(Option<String>, Option<Table>)>,

    /// List of deferred label resolutions. Each entry is a pair of (label, insn_reference).
    deferred_label_resolutions: Vec<(BranchOffset, InsnReference)>,

    /// Bitmask of cursors that have emitted a SeekRowid instruction.
    seekrowid_emitted_bitmask: u64,

    /// map of instruction index to manual comment (used in EXPLAIN)
    comments: HashMap<BranchOffset, &'static str>,
}

impl ProgramBuilder {
    pub fn new() -> Self {
        Self {
            nextFreeRegister: 1,
            nextFreeLabel: 0,
            nextFreeCursorId: 0,
            insns: Vec::new(),
            unresolvedInsnIndexes: Vec::new(),
            next_insn_label: None,
            tblNameTbls: Vec::new(),
            constant_insns: Vec::new(),
            deferred_label_resolutions: Vec::new(),
            seekrowid_emitted_bitmask: 0,
            comments: HashMap::new(),
        }
    }

    pub fn allocRegister(&mut self) -> usize {
        let reg = self.nextFreeRegister;
        self.nextFreeRegister += 1;
        reg
    }

    pub fn allocRegisters(&mut self, amount: usize) -> usize {
        let reg = self.nextFreeRegister;
        self.nextFreeRegister += amount;
        reg
    }

    pub fn next_free_register(&self) -> usize {
        self.nextFreeRegister
    }

    pub fn allocCursorId(&mut self, tblName: Option<String>, tbl: Option<Table>) -> usize {
        let cursor = self.nextFreeCursorId;
        self.nextFreeCursorId += 1;
        self.tblNameTbls.push((tblName, tbl));
        assert_eq!(self.tblNameTbls.len(), self.nextFreeCursorId);
        cursor
    }

    fn addInsn(&mut self, insn: Insn) {
        self.insns.push(insn);
    }

    pub fn addInsn0(&mut self, insn: Insn) {
        self.addInsn(insn);

        if let Some(label) = self.next_insn_label {
            self.next_insn_label = None;
            self.resolveLabel(label, (self.insns.len() - 1) as BranchOffset);
        }
    }

    pub fn add_comment(&mut self, insn_index: BranchOffset, comment: &'static str) {
        self.comments.insert(insn_index, comment);
    }

    // Emit an instruction that will be put at the end of the program (after Transaction statement).
    // This is useful for instructions that otherwise will be unnecessarily repeated in a loop.
    // Example: In `SELECT * from users where name='John'`, it is unnecessary to set r[1]='John' as we SCAN users table.
    // We could simply set it once before the SCAN started.
    pub fn mark_last_insn_constant(&mut self) {
        self.constant_insns.push(self.insns.pop().unwrap());
    }

    pub fn emit_constant_insns(&mut self) {
        self.insns.append(&mut self.constant_insns);
    }

    // insn 变为 label 的 unresolvedInsn1员
    pub fn addInsnWithLabelDependency(&mut self, insn: Insn, label: BranchOffset) {
        self.addInsn(insn);

        let labelIndex = self.label2Index(label);
        assert!(labelIndex < self.unresolvedInsnIndexes.len());

        // 上边的insn对应的index的
        let lastInsnIndex = (self.insns.len() - 1);
        assert!(lastInsnIndex >= 0);
        assert!(label < 0);

        &mut self.unresolvedInsnIndexes[labelIndex].push(lastInsnIndex);
    }

    pub fn nextPc(&self) -> BranchOffset {
        self.insns.len() as BranchOffset
    }

    // 应该是 allocPc的
    pub fn allocateLabel(&mut self) -> BranchOffset {
        self.nextFreeLabel -= 1;
        self.unresolvedInsnIndexes.push(Vec::new());

        self.nextFreeLabel
    }

    // Effectively a GOTO <next insn> without the need to emit an explicit GOTO instruction.
    // Useful when you know you need to jump to "the next part", but the exact offset is unknowable
    // at the time of emitting the instruction.
    pub fn preassignLabelToNextInsn(&mut self, label: BranchOffset) {
        self.next_insn_label = Some(label);
    }

    fn label2Index(&self, label: BranchOffset) -> usize {
        (label.abs() - 1) as usize
    }

    pub fn defer_label_resolution(&mut self, label: BranchOffset, insn_reference: InsnReference) {
        self.deferred_label_resolutions.push((label, insn_reference));
    }

    pub fn resolveLabel(&mut self, label: BranchOffset, targetPc: BranchOffset) {
        assert!(label < 0);
        assert!(targetPc >= 0);

        let labelIndex = self.label2Index(label);
        assert!(labelIndex < self.unresolvedInsnIndexes.len(), "Forbidden resolve of an unexistent label!");

        let unresolvedInsnIndexVec = &mut self.unresolvedInsnIndexes[labelIndex];

        for unresolvedInsnIndex in unresolvedInsnIndexVec.iter() {
            match &mut self.insns[*unresolvedInsnIndex] {
                Insn::Init { target_pc } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Eq { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Ne { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Lt { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Le { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Gt { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Ge { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::If { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::IfNot { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::RewindAwait { pc_if_empty, .. } => {
                    assert!(*pc_if_empty < 0);
                    *pc_if_empty = targetPc;
                }
                Insn::LastAwait { pc_if_empty, .. } => {
                    assert!(*pc_if_empty < 0);
                    *pc_if_empty = targetPc;
                }
                Insn::Goto { targetPc: target_pc } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::DecrJumpZero { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::SorterNext { pc_if_next, .. } => {
                    assert!(*pc_if_next < 0);
                    *pc_if_next = targetPc;
                }
                Insn::SorterSort { pc_if_empty, .. } => {
                    assert!(*pc_if_empty < 0);
                    *pc_if_empty = targetPc;
                }
                Insn::NotNull { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::IfPos { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::NextAwait { pc_if_next, .. } => {
                    assert!(*pc_if_next < 0);
                    *pc_if_next = targetPc;
                }
                Insn::PrevAwait { pc_if_next, .. } => {
                    assert!(*pc_if_next < 0);
                    *pc_if_next = targetPc;
                }
                Insn::InitCoroutine { jump_on_definition, .. } => *jump_on_definition = targetPc,
                Insn::NotExists { target_pc, .. } => *target_pc = targetPc,
                Insn::Yield { end_offset, .. } => *end_offset = targetPc,
                Insn::SeekRowid { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Gosub { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::Jump { target_pc_eq, .. } => {
                    // FIXME: this current implementation doesnt scale for insns that
                    // have potentially multiple label dependencies.
                    assert!(*target_pc_eq < 0);
                    *target_pc_eq = targetPc;
                }
                Insn::SeekGE { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::SeekGT { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::IdxGE { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::IdxGT { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                Insn::IsNull { target_pc, .. } => {
                    assert!(*target_pc < 0);
                    *target_pc = targetPc;
                }
                _ => todo!(),
            }
        }

        unresolvedInsnIndexVec.clear();
    }

    // translate table to cursor id
    pub fn resolveCursorId(&self, table_identifier: &str) -> CursorID {
        self.tblNameTbls.iter().position(|(tblName, _)| {
            tblName.as_ref().is_some_and(|ident| ident == table_identifier)
        }).unwrap()
    }

    pub fn resolve_deferred_labels(&mut self) {
        for i in 0..self.deferred_label_resolutions.len() {
            let (label, insn_reference) = self.deferred_label_resolutions[i];
            self.resolveLabel(label, insn_reference as BranchOffset);
        }
        self.deferred_label_resolutions.clear();
    }

    pub fn build(self,
                 dbHeader: Rc<RefCell<DbHeader>>,
                 conn: Weak<Conn>) -> Program {
        assert!(self.deferred_label_resolutions.is_empty(), "deferred_label_resolutions is not empty when build() is called, did you forget to call resolve_deferred_labels()?");
        assert!(self.constant_insns.is_empty(), "constant_insns is not empty when build() is called, did you forget to call emit_constant_insns()?");
        Program {
            max_registers: self.nextFreeRegister,
            insns: self.insns,
            cursor_ref: self.tblNameTbls,
            database_header: dbHeader,
            comments: self.comments,
            conn,
            auto_commit: true,
        }
    }
}
