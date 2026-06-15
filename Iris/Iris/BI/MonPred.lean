/-
Copyright (c) 2025 lean-vst contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI.BI
public import Iris.BI.BIBase
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

-- @ Coq iris.bi.monpred: monPredO / monPred_dist / monPred_equiv
/-- Pointwise OFE on monotone predicates (Coq `monPredO`):
`P ≡ Q := ∀ i, P i ≡ Q i` and `P ≡{n}≡ Q := ∀ i, P i ≡{n}≡ Q i`. -/
noncomputable instance : OFE (MonPred I PROP) where
  Equiv P Q := ∀ i, P.monPred_at i ≡ Q.monPred_at i
  Dist n P Q := ∀ i, P.monPred_at i ≡{n}≡ Q.monPred_at i
  dist_eqv := sorry
  equiv_dist := sorry
  dist_lt := sorry

-- @ Coq iris.bi.monpred: monPredC / monPred_compl (COFE completeness)
/-- Pointwise COFE on monotone predicates (Coq `monPredC`). The limit is taken
index-wise in the base BI. -/
noncomputable instance : IsCOFE (MonPred I PROP) where
  compl := sorry
  conv_compl := sorry

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
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_or_def — (P ∨ Q) i := P i ∨ Q i
/-- Disjunction, pointwise. -/
def or (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∨ Q.monPred_at i)
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_impl_def — (P → Q) := upclosed (λ i, P i → Q i)
/-- Implication (Kripke): up-closed so the result stays monotone. -/
def imp (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i → Q.monPred_at i))
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_forall_def — (∀ x, Φ x) i := ∀ x, Φ x i
/-- Universal quantification over `PROP`-valued predicates, lifted pointwise.
For iris-lean's predicate-form `sForall (Ψ : MonPred I PROP → Prop)`, the index
`i` projection ranges over the `monPred_at i` of all witnesses of `Ψ`. -/
def sForall (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sForall (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_exist_def — (∃ x, Φ x) i := ∃ x, Φ x i
/-- Existential quantification over `PROP`-valued predicates, lifted pointwise. -/
def sExists (Ψ : MonPred I PROP → Prop) : MonPred I PROP where
  monPred_at i := BIBase.sExists (fun p => ∃ q : MonPred I PROP, Ψ q ∧ q.monPred_at i = p)
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_sep_def — (P ∗ Q) i := P i ∗ Q i
/-- Separating conjunction, pointwise. -/
def sep (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(P.monPred_at i ∗ Q.monPred_at i)
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_wand_def — (P -∗ Q) := upclosed (λ i, P i -∗ Q i)
/-- Separating implication (Kripke): up-closed. -/
def wand (P Q : MonPred I PROP) : MonPred I PROP where
  monPred_at := MonPred.upclosed (fun i => iprop(P.monPred_at i -∗ Q.monPred_at i))
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_persistently_def — (<pers> P) i := <pers> (P i)
/-- Persistency modality, pointwise. -/
def persistently (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(<pers> (P.monPred_at i))
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_later_def — (▷ P) i := ▷ (P i)
/-- Later modality, pointwise. -/
def later (P : MonPred I PROP) : MonPred I PROP where
  monPred_at i := iprop(▷ (P.monPred_at i))
  monPred_mono _ := sorry

-- @ Coq iris.bi.monpred: monPred_in_def — (monPred_in j) i := ⌜j ⊑ i⌝
/-- `monPred_in j` holds at index `i` iff `j ⊑ i`. The canonical "I am at least
at index `j`" assertion. -/
def monPred_in (j : I.car) : MonPred I PROP where
  monPred_at i := iprop(⌜I.rel j i⌝)
  monPred_mono _ := sorry

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

-- @ Coq iris.bi.monpred: monPred_bi (BI mixin — all proof fields sorry)
noncomputable instance : BI (MonPred I PROP) where
  entails_preorder := sorry
  equiv_iff := sorry
  and_ne := sorry
  or_ne := sorry
  imp_ne := sorry
  sForall_ne := sorry
  sExists_ne := sorry
  sep_ne := sorry
  wand_ne := sorry
  persistently_ne := sorry
  later_ne := sorry
  pure_intro := sorry
  pure_elim' := sorry
  and_elim_l := sorry
  and_elim_r := sorry
  and_intro := sorry
  or_intro_l := sorry
  or_intro_r := sorry
  or_elim := sorry
  imp_intro := sorry
  imp_elim := sorry
  sForall_intro := sorry
  sForall_elim := sorry
  sExists_intro := sorry
  sExists_elim := sorry
  sep_mono := sorry
  emp_sep := sorry
  sep_symm := sorry
  sep_assoc_l := sorry
  wand_intro := sorry
  wand_elim := sorry
  persistently_mono := sorry
  persistently_idem_2 := sorry
  persistently_emp_2 := sorry
  persistently_and_2 := sorry
  persistently_sExists_1 := sorry
  persistently_absorb_l := sorry
  persistently_and_l := sorry
  later_mono := sorry
  later_intro := sorry
  later_sForall_2 := sorry
  later_sExists_false := sorry
  later_sep := sorry
  later_persistently := sorry
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
    (iprop(emp) : MonPred I PROP).monPred_at i ⊣⊢ iprop(emp) := sorry

-- @ Coq iris.bi.monpred: monPred_at_pure
theorem monPred_at_pure (i : I.car) (φ : Prop) :
    (iprop(⌜φ⌝) : MonPred I PROP).monPred_at i ⊣⊢ iprop(⌜φ⌝) := sorry

-- @ Coq iris.bi.monpred: monPred_at_and
theorem monPred_at_and (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∧ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∧ Q.monPred_at i) := sorry

-- @ Coq iris.bi.monpred: monPred_at_or
theorem monPred_at_or (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∨ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∨ Q.monPred_at i) := sorry

-- @ Coq iris.bi.monpred: monPred_at_impl (Kripke form)
theorem monPred_at_impl (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P → Q)).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel i j⌝ → (P.monPred_at j → Q.monPred_at j)) := sorry

-- @ Coq iris.bi.monpred: monPred_at_forall
theorem monPred_at_forall {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∀ x, Φ x)).monPred_at i ⊣⊢ iprop(∀ x, (Φ x).monPred_at i) := sorry

-- @ Coq iris.bi.monpred: monPred_at_exist
theorem monPred_at_exist {α : Sort _} (i : I.car) (Φ : α → MonPred I PROP) :
    (iprop(∃ x, Φ x)).monPred_at i ⊣⊢ iprop(∃ x, (Φ x).monPred_at i) := sorry

-- @ Coq iris.bi.monpred: monPred_at_sep
theorem monPred_at_sep (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P ∗ Q)).monPred_at i ⊣⊢ iprop(P.monPred_at i ∗ Q.monPred_at i) := sorry

-- @ Coq iris.bi.monpred: monPred_at_wand (Kripke form)
theorem monPred_at_wand (i : I.car) (P Q : MonPred I PROP) :
    (iprop(P -∗ Q)).monPred_at i ⊣⊢
      iprop(∀ j, ⌜I.rel i j⌝ → (P.monPred_at j -∗ Q.monPred_at j)) := sorry

-- @ Coq iris.bi.monpred: monPred_at_persistently
theorem monPred_at_persistently (i : I.car) (P : MonPred I PROP) :
    (iprop(<pers> P)).monPred_at i ⊣⊢ iprop(<pers> (P.monPred_at i)) := sorry

-- @ Coq iris.bi.monpred: monPred_at_later
theorem monPred_at_later (i : I.car) (P : MonPred I PROP) :
    (iprop(▷ P)).monPred_at i ⊣⊢ iprop(▷ (P.monPred_at i)) := sorry

-- @ Coq iris.bi.monpred: monPred_at_in
theorem monPred_at_in (i j : I.car) :
    (MonPred.monPred_in j : MonPred I PROP).monPred_at i ⊣⊢ iprop(⌜I.rel j i⌝) := sorry

-- @ Coq iris.bi.monpred: monPred_at_embed
theorem monPred_at_embed (i : I.car) (P : PROP) :
    (MonPred.embed P : MonPred I PROP).monPred_at i ⊣⊢ P := sorry

-- @ Coq iris.bi.monpred: monPred_at_objectively
theorem monPred_at_objectively (i : I.car) (P : MonPred I PROP) :
    (MonPred.objectively P).monPred_at i ⊣⊢ iprop(∀ j, P.monPred_at j) := sorry

-- @ Coq iris.bi.monpred: monPred_at_subjectively
theorem monPred_at_subjectively (i : I.car) (P : MonPred I PROP) :
    (MonPred.subjectively P).monPred_at i ⊣⊢ iprop(∃ j, P.monPred_at j) := sorry

end MonPred

end Iris.BI
