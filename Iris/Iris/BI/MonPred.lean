/-
Copyright (c) 2025 lean-vst contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.BI
public import Iris.BI.BIBase
public import Iris.BI.DerivedLaws
public import Iris.Algebra.OFE
public import Iris.Std.Classes

@[expose] public section

/-
Port of `iris.bi.monpred` (monotone predicates over a `BiIndex`, a.k.a. the
"monPred" / Kripke construction of a BI from a base BI).

Reference: Coq Iris `iris/bi/monpred.v`.

This is an INTERFACE PORT for lean-vst: signatures are 1:1 with Coq monpred.v,
but all `def` bodies that produce data are concrete (so that downstream code can
compute / unfold) while every `BI`/`OFE`/`COFE` mixin PROOF field and every
"unfold lemma" is left as `sorry` (to be discharged in a later phase). The goal
is that `assert := MonPred environ_index IProp` in the main repo type-checks.

iris-lean specifics (vs Coq):
- The base BI `PROP` uses iris-lean's `BIBase`/`BI` classes (fields
  `Entails emp pure and or imp sForall sExists sep wand persistently later`).
- `BI extends COFE`, so a `COFE (MonPred I PROP)` instance is required; it is
  provided pointwise with sorry'd proofs.
- iris-lean uses predicate-style `sForall`/`sExists : (PROP → Prop) → PROP`
  rather than Coq's index-family `∀ x, Φ x`. The MonPred lifting collects the
  per-index projections of the witnesses (mirrors the UPred / Classical
  instances).
- There is no `BiEmbed` typeclass in this iris-lean snapshot, so the embedding
  `⎡·⎤` is provided as a plain `def MonPred.embed` (not a class instance).
-/

namespace Iris.BI
open Iris Iris.Std OFE

/- ------------------------------------------------------------------ -/
/- `BiIndex`: the index preorder of a monotone-predicate BI.          -/
/- ------------------------------------------------------------------ -/

-- @ Coq iris.bi.monpred: biIndex
/-- A `BiIndex` is an inhabited type equipped with a preorder `⊑`.
Monotone predicates are functions out of a `BiIndex` that are monotone w.r.t.
this order. -/
structure BiIndex where
  /-- The carrier type of indices. -/
  car : Type _
  /-- The index type is inhabited (Coq `bi_index_inhabited`). -/
  [inhabited : Inhabited car]
  /-- The order on indices (Coq `bi_index_rel`). -/
  rel : car → car → Prop
  /-- The order is a preorder (Coq `bi_index_rel_preorder`). -/
  [preorder : Std.Preorder rel]

attribute [instance] BiIndex.inhabited BiIndex.preorder

instance : CoeSort BiIndex (Type _) := ⟨BiIndex.car⟩

/-- Notation for the `BiIndex` order, written `i ⊑ j` in Coq. -/
scoped infix:40 " ⊑ᵢ " => BiIndex.rel _

/- ------------------------------------------------------------------ -/
/- `MonPred`: monotone predicates `I → PROP`.                         -/
/- ------------------------------------------------------------------ -/

-- @ Coq iris.bi.monpred: monPred
/-- A monotone predicate over `BiIndex` `I` valued in the base BI `PROP`:
a function `monPred_at : I → PROP` that is monotone w.r.t. the index order
(`i ⊑ j → monPred_at i ⊢ monPred_at j`). -/
structure MonPred (I : BiIndex) (PROP : Type _) [BIBase PROP] where
  /-- The underlying index-indexed family (Coq `monPred_at`). -/
  monPred_at : I.car → PROP
  /-- Monotonicity in the index (Coq `monPred_mono`: `Proper ((⊑) ==> (⊢))`). -/
  monPred_mono : ∀ {i j : I.car}, I.rel i j → (monPred_at i ⊢ monPred_at j)

namespace MonPred

variable {I : BiIndex} {PROP : Type _} [BIBase PROP]

-- @ Coq iris.bi.monpred: monPred_at (accessor) — already a structure projection.

/-- Extensionality for `MonPred`: two monotone predicates are equal when their
`monPred_at` projections agree (Coq `monPred_at_inj` / `monPred_equiv`).
Proof obligation is proof-irrelevant on the `monPred_mono` field. -/
theorem ext {P Q : MonPred I PROP} (h : ∀ i, P.monPred_at i = Q.monPred_at i) :
    P = Q := by
  cases P; cases Q
  simp only [MonPred.mk.injEq]
  exact funext h

/- ------------------------------------------------------------------ -/
/- `upclosed`: the Kripke up-closure used for `impl` and `wand`.       -/
/- ------------------------------------------------------------------ -/

-- @ Coq iris.bi.monpred: monPred_upclosed
/-- Kripke up-closure of an index-indexed `PROP`-family:
`upclosed Φ i := ∀ j, ⌜i ⊑ j⌝ → Φ j`. Used by the `impl`/`wand` connectives so
that the result is monotone. -/
def upclosed [BI PROP] (Φ : I.car → PROP) : I.car → PROP :=
  fun i => iprop(∀ j, ⌜I.rel i j⌝ → Φ j)

end MonPred

/- ================================================================== -/
/- OFE / COFE structure on `MonPred I PROP` (pointwise; proofs sorry). -/
/- ================================================================== -/

section OFE
variable {I : BiIndex} {PROP : Type _} [BI PROP]

-- @ Coq iris.bi.monpred: monPredO / monPred_dist / monPred_equiv (Equiv/Dist pointwise).
-- Pointwise OFE: `P ≡ Q := ∀ i, P i ≡ Q i`, `P ≡{n}≡ Q := ∀ i, P i ≡{n}≡ Q i`.
noncomputable instance : OFE (MonPred I PROP) where
  Equiv P Q := ∀ i, P.monPred_at i ≡ Q.monPred_at i
  Dist n P Q := ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i
  dist_eqv :=
    { refl _ _ := dist_eqv.refl _
      symm h i := dist_eqv.symm (h i)
      trans h1 h2 i := dist_eqv.trans (h1 i) (h2 i) }
  equiv_dist {_ _} := by simp only [equiv_dist]; exact forall_comm
  dist_lt h1 h2 i := dist_lt (h1 i) h2

/-- Project a `MonPred` to its underlying `I.car → PROP` family as an OFE morphism
(Coq `monPred_sig`); non-expansive because `Dist` on `MonPred` is definitionally pointwise.
Used to take the COFE limit index-wise. -/
def atHom : MonPred I PROP -n> (I.car → PROP) where
  f P := P.monPred_at
  ne.1 _ _ _ h := h

-- @ Coq iris.bi.monpred: monPredC / monPred_compl (COFE completeness)
/-- Pointwise COFE on monotone predicates (Coq `monPredC`). The limit is taken
index-wise in the base BI. -/
noncomputable instance : IsCOFE (MonPred I PROP) where
  compl c :=
    { monPred_at := fun i => COFE.compl (c.map atHom) i
      monPred_mono := fun {i j} h =>
        LimitPreserving.entails (applyHom i) (applyHom j) (c.map atHom)
          (fun n => (c n).monPred_mono h) }
  conv_compl {n c} := IsCOFE.conv_compl (c := c.map atHom) (n := n)

end OFE

/- ================================================================== -/
/- `BIBase` instance: the separation-logic connectives.               -/
/- ================================================================== -/

namespace MonPred
variable {I : BiIndex} {PROP : Type _}

-- The connectives that don't use the Kripke closure only need `BIBase PROP`,
-- but `impl`/`wand`/`upclosed` need a full `BI PROP` (for the `∀`/`⌜·⌝` BI ops).
-- We therefore phrase the whole `BIBase (MonPred I PROP)` instance under
-- `[BI PROP]`, matching Coq (where the base is always a `bi`).

variable [BI PROP]

-- @ Coq iris.bi.monpred: monPred_entails
/-- Entailment of monotone predicates: pointwise base entailment
(Coq `monPred_entails P Q := ∀ i, P i ⊢ Q i`). -/
def Entails (P Q : MonPred I PROP) : Prop := ∀ i, P.monPred_at i ⊢ Q.monPred_at i

-- @ Coq iris.bi.monpred: monPred_emp_def — emp i := emp
/-- Unit of separation, pointwise. -/
def emp : MonPred I PROP where
  monPred_at _ := iprop(emp)
  monPred_mono _ := .rfl

-- @ Coq iris.bi.monpred: monPred_pure_def — pure φ i := ⌜φ⌝
/-- Pure embedding, index-independent. -/
def pure (φ : Prop) : MonPred I PROP where
  monPred_at _ := iprop(⌜φ⌝)
  monPred_mono _ := .rfl

-- @ Coq iris.bi.monpred: monPred_and_def — (P ∧ Q) i := P i ∧ Q i
/-- Conjunction, pointwise. -/
def and (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∧ Q.monPred_at i)
  monPred_mono h := and_mono (P.monPred_mono h) (Q.monPred_mono h)

-- @ Coq iris.bi.monpred: monPred_or_def — (P ∨ Q) i := P i ∨ Q i
/-- Disjunction, pointwise. -/
def or (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∨ Q.monPred_at i)
  monPred_mono h := or_mono (P.monPred_mono h) (Q.monPred_mono h)

-- @ Coq iris.bi.monpred: monPred_impl_def — (P → Q) := upclosed (λ i, P i → Q i)
/-- Implication (Kripke): up-closed so the result stays monotone. -/
def imp (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i → Q.monPred_at i))
  monPred_mono h :=
    forall_intro fun k => (forall_elim k).trans
      (imp_mono_left (pure_mono fun hjk => Transitive.trans h hjk))

-- @ Coq iris.bi.monpred: monPred_forall_def — (∀ x, Φ x) i := ∀ x, Φ x i
/-- Universal quantification over `PROP`-valued predicates, lifted pointwise.
For iris-lean's predicate-form `sForall (Ψ : MonPred I PROP → Prop)`, the index
`i` projection ranges over the `monPred_at i` of all witnesses of `Ψ`. -/
def sForall (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sForall (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono h :=
    sForall_intro fun p ⟨q, hq, hp⟩ => (sForall_elim ⟨q, hq, rfl⟩).trans (hp ▸ q.monPred_mono h)

-- @ Coq iris.bi.monpred: monPred_exist_def — (∃ x, Φ x) i := ∃ x, Φ x i
/-- Existential quantification over `PROP`-valued predicates, lifted pointwise. -/
def sExists (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sExists (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono h :=
    sExists_elim fun p ⟨q, hq, hp⟩ => (hp ▸ q.monPred_mono h).trans (sExists_intro ⟨q, hq, rfl⟩)

-- @ Coq iris.bi.monpred: monPred_sep_def — (P ∗ Q) i := P i ∗ Q i
/-- Separating conjunction, pointwise. -/
def sep (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∗ Q.monPred_at i)
  monPred_mono h := sep_mono (P.monPred_mono h) (Q.monPred_mono h)

-- @ Coq iris.bi.monpred: monPred_wand_def — (P -∗ Q) := upclosed (λ i, P i -∗ Q i)
/-- Separating implication (Kripke): up-closed. -/
def wand (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i -∗ Q.monPred_at i))
  monPred_mono h :=
    forall_intro fun k => (forall_elim k).trans
      (imp_mono_left (pure_mono fun hjk => Transitive.trans h hjk))

-- @ Coq iris.bi.monpred: monPred_persistently_def — (<pers> P) i := <pers> (P i)
/-- Persistency modality, pointwise. -/
def persistently (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(<pers> (P.monPred_at i))
  monPred_mono h := persistently_mono (P.monPred_mono h)

-- @ Coq iris.bi.monpred: monPred_later_def — (▷ P) i := ▷ (P i)
/-- Later modality, pointwise. -/
def later (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(▷ (P.monPred_at i))
  monPred_mono h := later_mono (P.monPred_mono h)

-- @ Coq iris.bi.monpred: monPred_in_def — (monPred_in j) i := ⌜j ⊑ i⌝
/-- `monPred_in j` holds at index `i` iff `j ⊑ i`. The canonical "I am at least
at index `j`" assertion. -/
def monPred_in (j : I.car) : MonPred I PROP where
  monPred_at i := iprop(⌜I.rel j i⌝)
  monPred_mono h := pure_mono fun hji => Transitive.trans hji h

-- @ Coq iris.bi.monpred: monPred_embed_def — ⎡P⎤ i := P
/-- Embedding of a base proposition as an index-independent monotone predicate
(Coq `monPred_embed` / `⎡·⎤`). There is no `BiEmbed` class in this iris-lean
snapshot, so this is a plain definition. -/
def embed (P : PROP) : MonPred I PROP where
  monPred_at _ := P
  monPred_mono _ := .rfl

-- @ Coq iris.bi.monpred: monPred_objectively_def — (<obj> P) i := ∀ i, P i
/-- The "objectively" modality: `<obj> P` forces `P` at *every* index, so the
result is index-independent. -/
def objectively (P : MonPred I PROP) : MonPred I PROP where
  monPred_at _ := iprop(∀ i, P.monPred_at i)
  monPred_mono _ := .rfl

-- @ Coq iris.bi.monpred: monPred_subjectively_def — (<subj> P) i := ∃ i, P i
/-- The "subjectively" modality: `<subj> P` holds if `P` holds at *some* index;
the result is index-independent. -/
def subjectively (P : MonPred I PROP) : MonPred I PROP where
  monPred_at _ := iprop(∃ i, P.monPred_at i)
  monPred_mono _ := .rfl

end MonPred

/- ------------------------------------------------------------------ -/
/- `BIBase`/`BI` typeclass instances.                                 -/
/- ------------------------------------------------------------------ -/

section Instances
variable {I : BiIndex} {PROP : Type _} [BI PROP]

-- @ Coq iris.bi.monpred: monPred_bi (BIBase part)
instance : BIBase (MonPred I PROP) where
  Entails       := MonPred.Entails
  emp           := MonPred.emp
  pure          := MonPred.pure
  and           := MonPred.and
  or            := MonPred.or
  imp           := MonPred.imp
  sForall       := MonPred.sForall
  sExists       := MonPred.sExists
  sep           := MonPred.sep
  wand          := MonPred.wand
  persistently  := MonPred.persistently
  later         := MonPred.later

-- @ Coq iris.bi.monpred: monPred_entails_at — entailment unfolds pointwise.
/-- MonPred entailment is *definitionally* the pointwise base entailment
(`BIBase.Entails := MonPred.Entails := ∀ i, P i ⊢ Q i`). This `Iff.rfl` helper
exposes that so BI-mixin proofs can `entails_at.mp h i` / `entails_at.mpr (fun i => …)`
— the iris-lean analog of Coq's `split=> i`. -/
theorem entails_at {P Q : MonPred I PROP} :
    (P ⊢ Q) ↔ ∀ i, P.monPred_at i ⊢ Q.monPred_at i := Iff.rfl

/-- MonPred OFE equivalence is *definitionally* pointwise (`Equiv P Q := ∀ i, P i ≡ Q i`). -/
theorem equiv_at {P Q : MonPred I PROP} :
    (P ≡ Q) ↔ ∀ i, P.monPred_at i ≡ Q.monPred_at i := Iff.rfl

/-- MonPred OFE distance is *definitionally* pointwise (`Dist n P Q := ∀ i, P i ≡{n}≡ Q i`). -/
theorem dist_at {n : Nat} {P Q : MonPred I PROP} :
    (P ≡{n}≡ Q) ↔ ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i := Iff.rfl

-- @ Coq iris.bi.monpred: monPred_bi (BI mixin — all proof fields sorry)
noncomputable instance : BI (MonPred I PROP) where
  entails_preorder :=
    { refl := entails_at.mpr fun _ => BIBase.Entails.rfl
      trans := fun h h' => entails_at.mpr fun i => (entails_at.mp h i).trans (entails_at.mp h' i) }
  equiv_iff := fun {P Q} =>
    ⟨fun h => ⟨entails_at.mpr fun i => (equiv_iff.mp (equiv_at.mp h i)).mp,
              entails_at.mpr fun i => (equiv_iff.mp (equiv_at.mp h i)).mpr⟩,
     fun h => equiv_at.mpr fun i => equiv_iff.mpr ⟨entails_at.mp h.1 i, entails_at.mp h.2 i⟩⟩
  and_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => and_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  or_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => or_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  imp_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i =>
    forall_ne fun j => imp_ne.ne Dist.rfl (imp_ne.ne (dist_at.mp h j) (dist_at.mp h' j))⟩
  sForall_ne := sorry
  sExists_ne := sorry
  sep_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i => sep_ne.ne (dist_at.mp h i) (dist_at.mp h' i)⟩
  wand_ne := ⟨fun _ _ _ h _ _ h' => dist_at.mpr fun i =>
    forall_ne fun j => imp_ne.ne Dist.rfl (wand_ne.ne (dist_at.mp h j) (dist_at.mp h' j))⟩
  persistently_ne := ⟨fun _ _ _ h => dist_at.mpr fun i => persistently_ne.ne (dist_at.mp h i)⟩
  later_ne := ⟨fun _ _ _ h => dist_at.mpr fun i => later_ne.ne (dist_at.mp h i)⟩
  pure_intro h := entails_at.mpr fun i => pure_intro h
  pure_elim' := fun {φ P} h => entails_at.mpr fun i => pure_elim' fun hφ => entails_at.mp (h hφ) i
  and_elim_l := entails_at.mpr fun i => and_elim_l
  and_elim_r := entails_at.mpr fun i => and_elim_r
  and_intro h h' := entails_at.mpr fun i => and_intro (entails_at.mp h i) (entails_at.mp h' i)
  or_intro_l := entails_at.mpr fun i => or_intro_l
  or_intro_r := entails_at.mpr fun i => or_intro_r
  or_elim h h' := entails_at.mpr fun i => or_elim (entails_at.mp h i) (entails_at.mp h' i)
  imp_intro {P Q R} h := entails_at.mpr fun i =>
    forall_intro fun j => imp_intro <| pure_elim_right fun (hij : I.rel i j) =>
      (P.monPred_mono hij).trans <| imp_intro (entails_at.mp h j)
  imp_elim {P Q R} h := entails_at.mpr fun i =>
    imp_elim <| (entails_at.mp h i).trans <|
      (forall_elim i).trans <| pure_imp_elim (Reflexive.refl : I.rel i i)
  sForall_intro h := entails_at.mpr fun i =>
    sForall_intro fun _ ⟨q, hΨ, hq⟩ => hq ▸ entails_at.mp (h q hΨ) i
  sForall_elim h := entails_at.mpr fun i => sForall_elim ⟨_, h, rfl⟩
  sExists_intro h := entails_at.mpr fun i => sExists_intro ⟨_, h, rfl⟩
  sExists_elim h := entails_at.mpr fun i =>
    sExists_elim fun _ ⟨q, hΨ, hq⟩ => hq ▸ entails_at.mp (h q hΨ) i
  sep_mono h h' := entails_at.mpr fun i => sep_mono (entails_at.mp h i) (entails_at.mp h' i)
  emp_sep := ⟨entails_at.mpr fun i => emp_sep.mp, entails_at.mpr fun i => emp_sep.mpr⟩
  sep_symm := entails_at.mpr fun i => sep_symm
  sep_assoc_l := entails_at.mpr fun i => sep_assoc_l
  wand_intro {P Q R} h := entails_at.mpr fun i => by
    refine forall_intro fun j => imp_intro ?_
    refine pure_elim_right fun (hij : I.rel i j) => ?_
    refine wand_intro (sep_symm.trans ?_)
    exact (sep_mono_right (P.monPred_mono hij)).trans (sep_symm.trans (entails_at.mp h j))
  wand_elim {P Q R} h := entails_at.mpr fun i =>
    (sep_mono_left ((entails_at.mp h i).trans
      ((forall_elim i).trans (pure_imp_elim (Reflexive.refl : I.rel i i))))).trans wand_elim_left
  persistently_mono h := entails_at.mpr fun i => persistently_mono (entails_at.mp h i)
  persistently_idem_2 := entails_at.mpr fun i => persistently_idem_2
  persistently_emp_2 := entails_at.mpr fun i => persistently_emp_2
  persistently_and_2 := entails_at.mpr fun i => persistently_and_2
  persistently_sExists_1 := sorry
  persistently_absorb_l := entails_at.mpr fun i => persistently_absorb_l
  persistently_and_l := entails_at.mpr fun i => persistently_and_l
  later_mono h := entails_at.mpr fun i => later_mono (entails_at.mp h i)
  later_intro := entails_at.mpr fun i => later_intro
  later_sForall_2 := sorry
  later_sExists_false := sorry
  later_sep := ⟨entails_at.mpr fun i => later_sep.mp, entails_at.mpr fun i => later_sep.mpr⟩
  later_persistently := ⟨entails_at.mpr fun i => later_persistently.mp, entails_at.mpr fun i => later_persistently.mpr⟩
  later_false_em := sorry

end Instances

/- ------------------------------------------------------------------ -/
/- `Objective` class.                                                 -/
/- ------------------------------------------------------------------ -/

-- @ Coq iris.bi.monpred: Objective
/-- A monotone predicate `P` is *objective* if its value does not depend on the
index: `P i ⊢ P j` for all `i j` (Coq `Objective`). Equivalently `P ⊣⊢ <obj> P`. -/
class Objective {I : BiIndex} {PROP : Type _} [BI PROP] (P : MonPred I PROP) : Prop where
  objective_at : ∀ i j : I.car, P.monPred_at i ⊢ P.monPred_at j

/- ================================================================== -/
/- Unfold lemmas (signatures 1:1 with Coq `monPred_at_*`; proofs sorry).-/
/- ================================================================== -/

namespace MonPred
variable {I : BiIndex} {PROP : Type _} [BI PROP]

-- @ Coq iris.bi.monpred: monPred_at_emp
theorem monPred_at_emp (i : I.car) :
    (iprop(emp) : MonPred I PROP).monPred_at i ⊣⊢ iprop(emp) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_pure
theorem monPred_at_pure (i : I.car) (φ : Prop) :
    (iprop(⌜φ⌝) : MonPred I PROP).monPred_at i ⊣⊢ iprop(⌜φ⌝) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_and
theorem monPred_at_and (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∧ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∧ Q.monPred_at i) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_or
theorem monPred_at_or (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∨ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∨ Q.monPred_at i) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_impl (Kripke form)
theorem monPred_at_impl (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P → Q)).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel i j⌝ → (P.monPred_at j → Q.monPred_at j)) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_forall
theorem monPred_at_forall {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∀ x, Φ x)).monPred_at i ⊣⊢ iprop(∀ x, (Φ x).monPred_at i) := by
  refine ⟨?_, ?_⟩
  · refine forall_intro fun x => ?_
    exact sForall_elim ⟨Φ x, ⟨x, rfl⟩, rfl⟩
  · refine sForall_intro fun p hp => ?_
    obtain ⟨P, ⟨x, hPx⟩, hp'⟩ := hp
    subst hPx; subst hp'
    exact forall_elim x

-- @ Coq iris.bi.monpred: monPred_at_exist
theorem monPred_at_exist {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∃ x, Φ x)).monPred_at i ⊣⊢ iprop(∃ x, (Φ x).monPred_at i) := by
  refine ⟨?_, ?_⟩
  · refine sExists_elim fun p hp => ?_
    obtain ⟨P, ⟨x, hPx⟩, hp'⟩ := hp
    subst hPx; subst hp'
    exact exists_intro (Ψ := fun y => (Φ y).monPred_at i) x
  · refine exists_elim fun x => ?_
    exact sExists_intro ⟨Φ x, ⟨x, rfl⟩, rfl⟩

-- @ Coq iris.bi.monpred: monPred_at_sep
theorem monPred_at_sep (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∗ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∗ Q.monPred_at i) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_wand (Kripke form)
theorem monPred_at_wand (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P -∗ Q)).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel i j⌝ → (P.monPred_at j -∗ Q.monPred_at j)) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_persistently
theorem monPred_at_persistently (i : I.car) (P : MonPred I PROP) :
    (iprop(<pers> P)).monPred_at i ⊣⊢ iprop(<pers> (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_later
theorem monPred_at_later (i : I.car) (P : MonPred I PROP) :
    (iprop(▷ P)).monPred_at i ⊣⊢ iprop(▷ (P.monPred_at i)) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_in
theorem monPred_at_in (i j : I.car) :
    (MonPred.monPred_in j : MonPred I PROP).monPred_at i ⊣⊢ iprop(⌜I.rel j i⌝) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_embed
theorem monPred_at_embed (i : I.car) (P : PROP) :
    (MonPred.embed P : MonPred I PROP).monPred_at i ⊣⊢ P :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_objectively
theorem monPred_at_objectively (i : I.car) (P : MonPred I PROP) :
    (MonPred.objectively P).monPred_at i ⊣⊢ iprop(∀ j, P.monPred_at j) :=
  BIBase.BiEntails.of_eq rfl

-- @ Coq iris.bi.monpred: monPred_at_subjectively
theorem monPred_at_subjectively (i : I.car) (P : MonPred I PROP) :
    (MonPred.subjectively P).monPred_at i ⊣⊢ iprop(∃ j, P.monPred_at j) :=
  BIBase.BiEntails.of_eq rfl

end MonPred

end Iris.BI
