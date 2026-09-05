/-
PROTOTYPE 2 — the α / fresh-naming question, in a NAMED calculus (isolated, imports only Mathlib
Finset). Complements EqProto.lean (which used de Bruijn, where α is automatic and the fresh-naming
issue is INVISIBLE).

Question (user): with equality DEFINED recursively, the neutral binder case must pick fresh names.
`Term.unpair`/`ctx_rest_MU` pick from ONE term's variables, so two α-equivalent terms could get
DIFFERENT fresh names.  Fix: `eqf` is BINARY, so it picks fresh from the COMBINED variable set and
uses that single choice for both sides.  Then α-variant binders normalise identically and the
α-equality rule (`pair_elim_alpha`) becomes DERIVABLE from reflexivity — not primitive.

Modelled with a single genuine binder `bind` (one component of `pair_elim`; the real `pair_elim`
binds two — the SAME mechanism applied twice).  `VarSymb.fresh = sup ∘ toNat, +1` is modelled by
`fresh s = s.sup id + 1` on `Var := ℕ`.
-/
import Mathlib.Data.Finset.Lattice.Fold

namespace EqProtoNamed

abbrev Var := ℕ

/-- Terms with one genuine binder `bind v body` (α-binds `v` in `body`). -/
inductive Tm where
  | var  : Var → Tm
  | pair : Tm → Tm → Tm
  | bind : Var → Tm → Tm
deriving DecidableEq

/-- All variables occurring in a term (free or bound) — the set fed to `fresh`. -/
def vars : Tm → Finset Var
  | .var x    => {x}
  | .pair a b => vars a ∪ vars b
  | .bind v b => insert v (vars b)

def size : Tm → Nat
  | .var _    => 1
  | .pair a b => size a + size b + 1
  | .bind _ b => size b + 1

/-- Canonical fresh choice: `sup (image toNat) + 1`, exactly `VarSymb.fresh` (here `toNat = id`;
    its `_not_mem` freshness lemma is standard — `VarSymb.fresh_not_mem`, QML_Full_v9:179 — and not
    needed for the α-derivation below, which turns on `rename_chain`, not on `fresh`'s value). -/
def fresh (s : Finset Var) : Var := s.sup id + 1

/-- Global renaming of `a` to `b` (capture-free when `b` is fresh, which is how we use it). -/
def rename (a b : Var) : Tm → Tm
  | .var x      => .var (if x = a then b else x)
  | .pair s t   => .pair (rename a b s) (rename a b t)
  | .bind v body => .bind (if v = a then b else v) (rename a b body)

theorem size_rename (a b : Var) (t : Tm) : size (rename a b t) = size t := by
  induction t with
  | var x => rfl
  | pair s t ihs iht => simp only [rename, size, ihs, iht]
  | bind v body ih => simp only [rename, size, ih]

/-- **Renaming chain**: `v ↦ c ↦ w` collapses to `v ↦ w`, provided `c` was fresh for the term.
    This is the algebraic fact behind "α-variants normalise to the same thing". -/
theorem rename_chain (v c w : Var) (t : Tm) (hc : c ∉ vars t) :
    rename c w (rename v c t) = rename v w t := by
  induction t with
  | var x =>
      simp only [vars, Finset.mem_singleton] at hc
      have hxc : x ≠ c := fun h => hc h.symm
      simp only [rename]
      by_cases hxv : x = v
      · subst hxv; simp
      · simp only [if_neg hxv, if_neg hxc]
  | pair s t ihs iht =>
      simp only [vars, Finset.mem_union, not_or] at hc
      simp only [rename, ihs hc.1, iht hc.2]
  | bind u body ih =>
      simp only [vars, Finset.mem_insert, not_or] at hc
      have huc : u ≠ c := fun h => hc.1 h.symm
      simp only [rename, ih hc.2]
      by_cases huv : u = v
      · subst huv; simp
      · simp only [if_neg huv, if_neg huc]

/-- Formulas: atomic equality on individuals, conjunction, and a binder `bindW`
    (the `pelimW` / witnessed-`□_x` analogue). -/
inductive Wff where
  | prim  : Tm → Tm → Wff
  | conj  : Wff → Wff → Wff
  | bindW : Var → Wff → Wff

/-- Minimal proof system: atomic reflexivity, ∧-intro, and congruence under the binder
    (necessitation). -/
inductive Pf : Wff → Prop where
  | primRefl : (t : Tm) → Pf (.prim t t)
  | conjI    : {p q : Wff} → Pf p → Pf q → Pf (.conj p q)
  | bindI    : {v : Var} → {p : Wff} → Pf p → Pf (.bindW v p)

/-- **Equality defined by recursion**, with the binder case picking a fresh name from the
    COMBINED variable set of BOTH terms and renaming both sides to it. -/
def eqf : Tm → Tm → Wff
  | .var x,    .var y    => .prim (.var x) (.var y)
  | .pair a b, .pair c d => .conj (eqf a c) (eqf b d)
  | .bind v a, .bind u b =>
      let w := fresh (vars (.bind v a) ∪ vars (.bind u b))
      .bindW w (eqf (rename v w a) (rename u w b))
  | _,         _         => .prim (.var 0) (.var 0)
termination_by t _ => size t
decreasing_by
  all_goals first
    | (simp only [size]; omega)
    | (rw [size_rename]; simp only [size]; omega)

/-- **Reflexivity** holds — the binder case uses `bindI` (necessitation) of the inner reflexivity,
    and both sides pick the *same* fresh name because the combined set is the same. -/
def eqf_refl : (t : Tm) → Pf (eqf t t)
  | .var x    => by simp only [eqf]; exact .primRefl _
  | .pair a b => by simp only [eqf]; exact .conjI (eqf_refl a) (eqf_refl b)
  | .bind v a => by simp only [eqf]; exact .bindI (eqf_refl _)
termination_by t => size t
decreasing_by
  all_goals first
    | (simp only [size]; omega)
    | (rw [size_rename]; simp only [size]; omega)

/-- **α-equality is DERIVABLE** (the `pair_elim_alpha` payoff): a binder and its α-variant
    (`v` renamed to a fresh `c`) are provably equal — from reflexivity + `rename_chain`, with NO
    primitive α rule.  The combined-set fresh choice is what makes the two bodies normalise to the
    *syntactically identical* `rename v w a`. -/
theorem alpha_derivable (v c : Var) (a : Tm) (hc : c ∉ vars a) :
    Pf (eqf (.bind v a) (.bind c (rename v c a))) := by
  simp only [eqf]
  -- The two renamed bodies collapse to the same term via `rename_chain`, so it is reflexivity.
  rw [rename_chain v c _ a hc]
  exact .bindI (eqf_refl _)

end EqProtoNamed

#print axioms EqProtoNamed.alpha_derivable
#print axioms EqProtoNamed.eqf_refl
#print axioms EqProtoNamed.rename_chain
