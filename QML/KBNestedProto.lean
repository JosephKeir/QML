import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Prototype: nested sequents for the propositional modal cube (without D), with cut

The test `docs/v12-modal-extensions.md` §12.37 asked for before any quantifier work: is cut
admissible when the sequent is a **tree** and a node can send information to nodes other than its
children (B: to the parent; 5: to siblings)?

* Formulas are in negation normal form; sequents are one-sided.
* A node of the tree is a **label** (a path of child indices from the root), and a sequent is a
  list of labelled formulas.  This is a nested sequent written flat: rules act at any node.
* `Sys`: which of T, B, 4, 5 hold.  `Acc S`: the tree's edges closed under the system's frame
  conditions.
* `Der S n Γ`: a cut-free derivation of height at most `n`.  The modal rules:
  * `box`: `□A` at `τ` opens a **fresh** child `τ.k` with `A`;
  * `dia`: `◇A` at `τ` puts `A` at any existing node `τ` sees (`Acc S`).
* `Der.subst`: derivations are closed under label maps sending edges to accessibilities.  In
  particular a fresh child can be **retargeted** to any node its parent sees (`Der.retarget`).
* ⭐`KBN.cut`: cut is admissible, at any node that has a formula — **one proof for all sixteen
  systems**: the frame conditions enter only through `AdjPres.adj`.
* `KBN.b_axiom`, `KBN.five_axiom`: `p → □◇p` with B, `◇p → □◇p` with 5.
-/

namespace KBN

/-- Formulas in negation normal form. -/
inductive Form where
  | atom : ℕ → Form
  | natom : ℕ → Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | box : Form → Form
  | dia : Form → Form
  deriving DecidableEq

namespace Form

/-- Negation, by duality. -/
def neg : Form → Form
  | atom p => natom p
  | natom p => atom p
  | and A B => or A.neg B.neg
  | or A B => and A.neg B.neg
  | box A => dia A.neg
  | dia A => box A.neg

def size : Form → ℕ
  | atom _ => 0
  | natom _ => 0
  | and A B => A.size + B.size + 1
  | or A B => A.size + B.size + 1
  | box A => A.size + 1
  | dia A => A.size + 1

@[simp] theorem neg_neg : ∀ A : Form, A.neg.neg = A
  | atom _ => rfl
  | natom _ => rfl
  | and A B => by simp [neg, neg_neg A, neg_neg B]
  | or A B => by simp [neg, neg_neg A, neg_neg B]
  | box A => by simp [neg, neg_neg A]
  | dia A => by simp [neg, neg_neg A]

@[simp] theorem size_neg : ∀ A : Form, A.neg.size = A.size
  | atom _ => rfl
  | natom _ => rfl
  | and A B => by simp [neg, size, size_neg A, size_neg B]
  | or A B => by simp [neg, size, size_neg A, size_neg B]
  | box A => by simp [neg, size, size_neg A]
  | dia A => by simp [neg, size, size_neg A]

end Form

/-- A node of the tree: the path of child indices from the root. -/
abbrev Lab := List ℕ

/-- A labelled formula. -/
abbrev LF := Lab × Form

/-- A system of the cube without D: which of T, B, 4, 5 hold. -/
structure Sys where
  T : Bool
  B : Bool
  Four : Bool
  Five : Bool

/-- ⭐**Accessibility between nodes**: the tree's edges, closed under the system's frame
    conditions.  K has the edges only; B adds the way back to the parent; 5 makes siblings see
    each other. -/
inductive Acc (S : Sys) : Lab → Lab → Prop where
  | edge (a : Lab) (i : ℕ) : Acc S a (a ++ [i])
  | refl (a : Lab) : S.T = true → Acc S a a
  | symm {a b : Lab} : S.B = true → Acc S a b → Acc S b a
  | trans {a b c : Lab} : S.Four = true → Acc S a b → Acc S b c → Acc S a c
  | eucl {a b c : Lab} : S.Five = true → Acc S a b → Acc S a c → Acc S b c

/-- No formula of `Γ` lies at `τ` or below it. -/
def Fresh (τ : Lab) (Γ : List LF) : Prop := ∀ x ∈ Γ, ¬ τ <+: x.1

/-- The node `τ` has a formula. -/
def Pop (τ : Lab) (Γ : List LF) : Prop := ∃ F, (τ, F) ∈ Γ

theorem Pop.mono {τ : Lab} {Γ Γ' : List LF} (h : Pop τ Γ) (hs : Γ ⊆ Γ') : Pop τ Γ' :=
  h.imp fun _ hF => hs hF

/-- ⭐**Cut-free derivations**, of height at most `n`. -/
inductive Der (S : Sys) : ℕ → List LF → Prop where
  | ax {n : ℕ} {Γ : List LF} (τ : Lab) (p : ℕ) :
      (τ, .atom p) ∈ Γ → (τ, .natom p) ∈ Γ → Der S n Γ
  | and {n : ℕ} {Γ : List LF} {τ : Lab} {A B : Form} :
      (τ, A.and B) ∈ Γ → Der S n ((τ, A) :: Γ) → Der S n ((τ, B) :: Γ) → Der S (n + 1) Γ
  | or {n : ℕ} {Γ : List LF} {τ : Lab} {A B : Form} :
      (τ, A.or B) ∈ Γ → Der S n ((τ, A) :: (τ, B) :: Γ) → Der S (n + 1) Γ
  /-- `□A` at `τ`: a fresh child with `A`. -/
  | box {n : ℕ} {Γ : List LF} {τ : Lab} {A : Form} (k : ℕ) :
      (τ, .box A) ∈ Γ → Fresh (τ ++ [k]) Γ → Der S n ((τ ++ [k], A) :: Γ) → Der S (n + 1) Γ
  /-- `◇A` at `τ`: `A` at any existing node `τ` sees. -/
  | dia {n : ℕ} {Γ : List LF} {τ τ' : Lab} {A : Form} :
      (τ, .dia A) ∈ Γ → Acc S τ τ' → Pop τ' Γ → Der S n ((τ', A) :: Γ) → Der S (n + 1) Γ

/-! ## Label maps -/

variable {S : Sys}

/-- A label map sending every edge of the tree to an accessibility. -/
def AdjPres (S : Sys) (f : Lab → Lab) : Prop := ∀ a i, Acc S (f a) (f (a ++ [i]))

/-- ⭐Such a map preserves accessibility: `Acc` is the closure of the edges, and is closed. -/
theorem AdjPres.adj {f : Lab → Lab} (hf : AdjPres S f) {a b : Lab} (h : Acc S a b) :
    Acc S (f a) (f b) := by
  induction h with
  | edge a i => exact hf a i
  | refl a hT => exact .refl _ hT
  | symm hB _ ih => exact .symm hB ih
  | trans hF _ _ ih₁ ih₂ => exact .trans hF ih₁ ih₂
  | eucl hV _ _ ih₁ ih₂ => exact .eucl hV ih₁ ih₂

theorem adjPres_id : AdjPres S id := fun a i => .edge a i

/-- `f`, with the subtree at `p` moved to `q`. -/
def moveSub (f : Lab → Lab) (p q : Lab) : Lab → Lab :=
  fun l => if p <+: l then q ++ l.drop p.length else f l

theorem moveSub_self (f : Lab → Lab) (p q : Lab) : moveSub f p q p = q := by
  simp [moveSub]

theorem moveSub_of_not {f : Lab → Lab} {p q l : Lab} (h : ¬ p <+: l) : moveSub f p q l = f l :=
  if_neg h

theorem adjPres_over {f : Lab → Lab} (hf : AdjPres S f) {τ q : Lab} (k : ℕ)
    (hq : Acc S (f τ) q) : AdjPres S (moveSub f (τ ++ [k]) q) := by
  intro a i
  by_cases h1 : τ ++ [k] <+: a
  · have h2 : τ ++ [k] <+: a ++ [i] := h1.trans (List.prefix_append _ _)
    simp only [moveSub, if_pos h1, if_pos h2]
    rw [List.drop_append_of_le_length h1.length_le, ← List.append_assoc]
    exact .edge _ i
  · by_cases h2 : τ ++ [k] <+: a ++ [i]
    · have he : τ ++ [k] = a ++ [i] := by
        rcases List.prefix_concat_iff.mp h2 with h | h
        · exact h
        · exact absurd h h1
      obtain ⟨rfl, -⟩ := List.append_inj' he rfl
      rw [moveSub_of_not h1, ← he, moveSub_self]
      exact hq
    · rw [moveSub_of_not h1, moveSub_of_not h2]
      exact hf a i

/-- A sequent along a label map. -/
def mapL (f : Lab → Lab) (Γ : List LF) : List LF := Γ.map fun x => (f x.1, x.2)

theorem mem_mapL {f : Lab → Lab} {Γ : List LF} {τ : Lab} {A : Form} (h : (τ, A) ∈ Γ) :
    (f τ, A) ∈ mapL f Γ :=
  List.mem_map.mpr ⟨(τ, A), h, rfl⟩

theorem mapL_over_fresh {f : Lab → Lab} {p q : Lab} {Γ : List LF} (h : Fresh p Γ) :
    mapL (moveSub f p q) Γ = mapL f Γ :=
  List.map_congr_left fun x hx => by rw [moveSub_of_not (h x hx)]

theorem mapL_id (Γ : List LF) : mapL id Γ = Γ := by
  simp [mapL]

/-- A fresh child exists. -/
theorem exists_fresh (τ : Lab) (Γ : List LF) : ∃ k, Fresh (τ ++ [k]) Γ := by
  have bound : ∀ l : List ℕ, ∃ k, ∀ x ∈ l, x < k := by
    intro l
    induction l with
    | nil => exact ⟨0, fun _ h => absurd h List.not_mem_nil⟩
    | cons a l ih =>
        obtain ⟨k, hk⟩ := ih
        refine ⟨max k (a + 1), fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
        · exact lt_of_lt_of_le (hk x hx) (le_max_left _ _)
  obtain ⟨k, hk⟩ := bound (Γ.flatMap fun x => x.1)
  refine ⟨k, fun x hx hp => ?_⟩
  have hmem : k ∈ x.1 := hp.subset (by simp)
  exact absurd (hk k (List.mem_flatMap.mpr ⟨x, hx, hmem⟩)) (lt_irrefl _)

namespace Der

/-- ⭐**Derivations along an adjacency-preserving label map**, height kept. -/
theorem subst {n : ℕ} {Γ : List LF} (d : Der S n Γ) :
    ∀ f : Lab → Lab, AdjPres S f → Der S n (mapL f Γ) := by
  induction d with
  | ax τ p h₁ h₂ => exact fun f _ => .ax (f τ) p (mem_mapL h₁) (mem_mapL h₂)
  | and h _ _ ih₁ ih₂ => exact fun f hf => .and (mem_mapL h) (ih₁ f hf) (ih₂ f hf)
  | or h _ ih => exact fun f hf => .or (mem_mapL h) (ih f hf)
  | @box n Γ τ A k h hfr _ ih =>
      intro f hf
      obtain ⟨m, hm⟩ := exists_fresh (f τ) (mapL f Γ)
      have := ih (moveSub f (τ ++ [k]) (f τ ++ [m])) (adjPres_over hf k (.edge _ m))
      change Der S n ((moveSub f (τ ++ [k]) (f τ ++ [m]) (τ ++ [k]), A) :: mapL _ Γ) at this
      rw [moveSub_self, mapL_over_fresh hfr] at this
      exact .box m (mem_mapL h) hm this
  | dia h hadj hpop _ ih =>
      exact fun f hf => .dia (mem_mapL h) (hf.adj hadj) (hpop.imp fun _ hF => mem_mapL hF)
        (ih f hf)

/-- ⭐**Retargeting a fresh child** to any neighbour of its parent: an existing child, or (B) the
    parent's own parent. -/
theorem retarget {n : ℕ} {Γ : List LF} {τ q : Lab} {k : ℕ} {A : Form}
    (d : Der S n ((τ ++ [k], A) :: Γ)) (hfr : Fresh (τ ++ [k]) Γ) (hq : Acc S τ q) :
    Der S n ((q, A) :: Γ) := by
  have := d.subst (moveSub id (τ ++ [k]) q) (adjPres_over adjPres_id k hq)
  change Der S n ((moveSub id (τ ++ [k]) q (τ ++ [k]), A) :: mapL _ Γ) at this
  rwa [moveSub_self, mapL_over_fresh hfr, mapL_id] at this

theorem mono_height {n : ℕ} {Γ : List LF} (d : Der S n Γ) : ∀ {m : ℕ}, n ≤ m → Der S m Γ := by
  induction d with
  | ax τ p h₁ h₂ => exact fun _ => .ax τ p h₁ h₂
  | and h _ _ ih₁ ih₂ =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .and h (ih₁ (by omega)) (ih₂ (by omega))
  | or h _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .or h (ih (by omega))
  | box k h hfr _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .box k h hfr (ih (by omega))
  | dia h hadj hpop _ ih =>
      intro m hm; obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .dia h hadj hpop (ih (by omega))

/-- ⭐**Weakening, exchange, contraction**, height kept.  The `box` case renames its fresh child
    away from the new formulas (`retarget`). -/
theorem weaken : ∀ (n : ℕ) {Γ Γ' : List LF}, Der S n Γ → Γ ⊆ Γ' → Der S n Γ' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ Γ' d hs
  cases d with
  | ax τ p h₁ h₂ => exact .ax τ p (hs h₁) (hs h₂)
  | and h p q =>
      exact .and (hs h) (ih _ (Nat.lt_succ_self _) p (List.cons_subset_cons _ hs))
        (ih _ (Nat.lt_succ_self _) q (List.cons_subset_cons _ hs))
  | or h p =>
      exact .or (hs h) (ih _ (Nat.lt_succ_self _) p
        (List.cons_subset_cons _ (List.cons_subset_cons _ hs)))
  | @box _ _ τ A k h hfr p =>
      obtain ⟨m, hm⟩ := exists_fresh τ Γ'
      have p' := p.retarget hfr (q := τ ++ [m]) (.edge _ m)
      exact .box m (hs h) hm (ih _ (Nat.lt_succ_self _) p' (List.cons_subset_cons _ hs))
  | dia h hadj hpop p =>
      exact .dia (hs h) hadj (hpop.mono hs)
        (ih _ (Nat.lt_succ_self _) p (List.cons_subset_cons _ hs))

end Der

theorem both {a b : ℕ} {Γ Γ' : List LF} (p : Der S a Γ) (q : Der S b Γ') :
    Der S (max a b) Γ ∧ Der S (max a b) Γ' :=
  ⟨p.mono_height (le_max_left _ _), q.mono_height (le_max_right _ _)⟩

/-! ## Cut -/

/-- The cut formula principal in the last rule, with that rule's premises. -/
inductive Prin (S : Sys) : LF → ℕ → List LF → Prop where
  | atom {τ : Lab} {p n : ℕ} {Γ : List LF} : (τ, .natom p) ∈ Γ → Prin S (τ, .atom p) n Γ
  | natom {τ : Lab} {p n : ℕ} {Γ : List LF} : (τ, .atom p) ∈ Γ → Prin S (τ, .natom p) n Γ
  | and {τ : Lab} {A B : Form} {n n' : ℕ} {Γ : List LF} : n' < n →
      Der S n' ((τ, A) :: (τ, A.and B) :: Γ) → Der S n' ((τ, B) :: (τ, A.and B) :: Γ) →
      Prin S (τ, A.and B) n Γ
  | or {τ : Lab} {A B : Form} {n n' : ℕ} {Γ : List LF} : n' < n →
      Der S n' ((τ, A) :: (τ, B) :: (τ, A.or B) :: Γ) → Prin S (τ, A.or B) n Γ
  | box {τ : Lab} {A : Form} {n n' : ℕ} {Γ : List LF} (k : ℕ) : n' < n →
      Fresh (τ ++ [k]) ((τ, .box A) :: Γ) → Der S n' ((τ ++ [k], A) :: (τ, .box A) :: Γ) →
      Prin S (τ, .box A) n Γ
  | dia {τ : Lab} {A : Form} {n n' : ℕ} {Γ : List LF} (τ' : Lab) : n' < n → Acc S τ τ' →
      Pop τ' Γ → Der S n' ((τ', A) :: (τ, .dia A) :: Γ) → Prin S (τ, .dia A) n Γ

theorem swap_sub {X Z : LF} {Γ Γ' : List LF} (h : Γ ⊆ Γ') : Z :: X :: Γ ⊆ X :: Z :: Γ' := by
  intro a ha
  simp only [List.mem_cons] at ha ⊢
  rcases ha with rfl | rfl | ha
  · exact .inr (.inl rfl)
  · exact .inl rfl
  · exact .inr (.inr (h ha))

/-- ⭐**The cut moves up one derivation** until the cut formula is principal there.  `hcut` is the
    induction hypothesis with the other derivation weakened. -/
theorem perm {n : ℕ} {X : LF} {Γ : List LF}
    (hcut : ∀ {Γ' : List LF} {n' : ℕ}, n' < n → Γ ⊆ Γ' → Der S n' (X :: Γ') → ∃ k, Der S k Γ')
    (hpop : Pop X.1 Γ) (d : Der S n (X :: Γ)) : (∃ k, Der S k Γ) ∨ Prin S X n Γ := by
  cases d with
  | ax τ p h₁ h₂ =>
      rcases List.mem_cons.mp h₁ with rfl | g₁
      · rcases List.mem_cons.mp h₂ with h | g₂
        · cases h
        · exact .inr (.atom g₂)
      · rcases List.mem_cons.mp h₂ with rfl | g₂
        · exact .inr (.natom g₁)
        · exact .inl ⟨0, .ax τ p g₁ g₂⟩
  | @and n' _ τ A B h p q =>
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr (.and (Nat.lt_succ_self _) p q)
      · obtain ⟨k₁, e₁⟩ := hcut (Nat.lt_succ_self _) (List.subset_cons_self _ _)
          (p.weaken _ (swap_sub (List.Subset.refl _)))
        obtain ⟨k₂, e₂⟩ := hcut (Nat.lt_succ_self _) (List.subset_cons_self _ _)
          (q.weaken _ (swap_sub (List.Subset.refl _)))
        exact .inl ⟨_, .and h (both e₁ e₂).1 (both e₁ e₂).2⟩
  | @or n' _ τ A B h p =>
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr (.or (Nat.lt_succ_self _) p)
      · obtain ⟨k, e⟩ := hcut (Γ' := (τ, A) :: (τ, B) :: Γ) (Nat.lt_succ_self _)
          (fun a ha => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))
          (p.weaken _ (by
            intro a ha
            simp only [List.mem_cons] at ha ⊢
            tauto))
        exact .inl ⟨_, .or h e⟩
  | @box n' _ τ A k h hfr p =>
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr (.box k (Nat.lt_succ_self _) hfr p)
      · obtain ⟨k', e⟩ := hcut (Nat.lt_succ_self _) (List.subset_cons_self _ _)
          (p.weaken _ (swap_sub (List.Subset.refl _)))
        exact .inl ⟨_, .box k h (fun x hx => hfr x (List.mem_cons_of_mem _ hx)) e⟩
  | @dia n' _ τ τ' A h hadj hp p =>
      have hp' : Pop τ' Γ := by
        obtain ⟨F, hF⟩ := hp
        rcases List.mem_cons.mp hF with rfl | hF
        · exact hpop
        · exact ⟨F, hF⟩
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr (.dia τ' (Nat.lt_succ_self _) hadj hp' p)
      · obtain ⟨k, e⟩ := hcut (Nat.lt_succ_self _) (List.subset_cons_self _ _)
          (p.weaken _ (swap_sub (List.Subset.refl _)))
        exact .inl ⟨_, .dia h hadj hp' e⟩

/-- The induction hypothesis: cut on a smaller formula, or one as large at smaller heights. -/
def CutIH (S : Sys) (s h : ℕ) : Prop :=
  ∀ {Γ : List LF} {σ : Lab} {A : Form} {n m : ℕ},
    (A.size < s ∨ A.size = s ∧ n + m < h) → Pop σ Γ →
    Der S n ((σ, A) :: Γ) → Der S m ((σ, A.neg) :: Γ) → ∃ k, Der S k Γ

macro "wk" : tactic =>
  `(tactic| (intro a ha; simp only [List.mem_cons] at ha ⊢; tauto))

/-- ⭐**One step of cut elimination.** -/
theorem cut_step {s h : ℕ} (ih : CutIH S s h) {Γ : List LF} {σ : Lab} {A : Form} {n m : ℕ}
    (hs : A.size = s) (hh : n + m = h) (hpop : Pop σ Γ) (d₁ : Der S n ((σ, A) :: Γ))
    (d₂ : Der S m ((σ, A.neg) :: Γ)) : ∃ k, Der S k Γ := by
  have pc : ∀ {Z : LF}, Pop σ (Z :: Γ) := hpop.mono (List.subset_cons_self _ _)
  rcases perm (X := (σ, A)) (fun {Γ' n'} hn hΓ e =>
      ih (.inr ⟨hs, by omega⟩) (hpop.mono hΓ) e
        (d₂.weaken _ (List.cons_subset_cons _ hΓ))) hpop d₁ with done | P₁
  · exact done
  rcases perm (X := (σ, A.neg)) (fun {Γ' m'} hm hΓ e =>
      ih (.inr ⟨hs, by omega⟩) (hpop.mono hΓ)
        (d₁.weaken _ (List.cons_subset_cons _ hΓ)) e) hpop d₂ with done | P₂
  · exact done
  cases A with
  | atom p =>
      cases P₁ with
      | atom hmem =>
          exact ⟨_, d₂.weaken _ (by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            exacts [hmem, ha])⟩
  | natom p =>
      cases P₁ with
      | natom hmem =>
          exact ⟨_, d₂.weaken _ (by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            exacts [hmem, ha])⟩
  | and A B =>
      have P₂' : Prin S (σ, A.neg.or B.neg) m Γ := P₂
      cases P₁ with
      | and hn pa pb =>
      cases P₂' with
      | or hm e =>
      have sA : A.size < s := by rw [← hs]; simp only [Form.size]; omega
      have sB : B.size < s := by rw [← hs]; simp only [Form.size]; omega
      obtain ⟨_, Da⟩ := ih (A := A.and B) (.inr ⟨hs, by omega⟩) pc
        (pa.weaken _ (swap_sub (List.Subset.refl _)))
        (d₂.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
      obtain ⟨_, Db⟩ := ih (A := A.and B) (.inr ⟨hs, by omega⟩) pc
        (pb.weaken _ (swap_sub (List.Subset.refl _)))
        (d₂.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
      obtain ⟨_, E⟩ := ih (A := A.and B) (Γ := (σ, A.neg) :: (σ, B.neg) :: Γ)
        (.inr ⟨hs, by omega⟩) (pc.mono (List.subset_cons_self _ _))
        (d₁.weaken _ (by wk)) (e.weaken _ (by wk))
      obtain ⟨_, F⟩ := ih (A := A) (Γ := (σ, B.neg) :: Γ) (.inl sA) pc
        (Da.weaken _ (by wk)) E
      exact ih (A := B) (.inl sB) hpop Db F
  | or A B =>
      have P₂' : Prin S (σ, A.neg.and B.neg) m Γ := P₂
      cases P₁ with
      | or hn pab =>
      cases P₂' with
      | and hm ea eb =>
      have sA : A.size < s := by rw [← hs]; simp only [Form.size]; omega
      have sB : B.size < s := by rw [← hs]; simp only [Form.size]; omega
      obtain ⟨_, Pab⟩ := ih (A := A.or B) (Γ := (σ, A) :: (σ, B) :: Γ)
        (.inr ⟨hs, by omega⟩) (pc.mono (List.subset_cons_self _ _))
        (pab.weaken _ (by wk)) (d₂.weaken _ (by wk))
      obtain ⟨_, Ea⟩ := ih (A := A.or B) (.inr ⟨hs, by omega⟩) pc
        (d₁.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
        (ea.weaken _ (swap_sub (List.Subset.refl _)))
      obtain ⟨_, Eb⟩ := ih (A := A.or B) (.inr ⟨hs, by omega⟩) pc
        (d₁.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
        (eb.weaken _ (swap_sub (List.Subset.refl _)))
      obtain ⟨_, F⟩ := ih (A := A) (Γ := (σ, B) :: Γ) (.inl sA) pc Pab
        (Ea.weaken _ (by wk))
      exact ih (A := B) (.inl sB) hpop F Eb
  | box A =>
      have P₂' : Prin S (σ, .dia A.neg) m Γ := P₂
      cases P₁ with
      | box k hn hfr p =>
      cases P₂' with
      | dia τ' hm hadj hp' e =>
      have sA : A.size < s := by rw [← hs]; simp only [Form.size]; omega
      -- the fresh child retargeted to the neighbour the `◇` rule used (a child, or the parent)
      have p' := p.retarget hfr hadj
      obtain ⟨_, D₁⟩ := ih (A := .box A) (.inr ⟨hs, by omega⟩) pc
        (p'.weaken _ (swap_sub (List.Subset.refl _)))
        (d₂.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
      obtain ⟨_, D₂⟩ := ih (A := .box A) (.inr ⟨hs, by omega⟩) pc
        (d₁.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
        (e.weaken _ (swap_sub (List.Subset.refl _)))
      exact ih (A := A) (.inl sA) hp' D₁ D₂
  | dia A =>
      have P₂' : Prin S (σ, .box A.neg) m Γ := P₂
      cases P₁ with
      | dia τ' hn hadj hp' p =>
      cases P₂' with
      | box k hm hfr e =>
      have sA : A.size < s := by rw [← hs]; simp only [Form.size]; omega
      have e' := e.retarget hfr hadj
      obtain ⟨_, D₁⟩ := ih (A := .dia A) (.inr ⟨hs, by omega⟩) pc
        (p.weaken _ (swap_sub (List.Subset.refl _)))
        (d₂.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
      obtain ⟨_, D₂⟩ := ih (A := .dia A) (.inr ⟨hs, by omega⟩) pc
        (d₁.weaken _ (List.cons_subset_cons _ (List.subset_cons_self _ _)))
        (e'.weaken _ (swap_sub (List.Subset.refl _)))
      exact ih (A := A) (.inl sA) hp' D₁ D₂

theorem cutIH_all : ∀ s h, CutIH S s h := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
    intro h
    induction h using Nat.strong_induction_on with
    | _ h ihh =>
      intro Γ σ A n m hlt hpop d₁ d₂
      rcases hlt with hlt | ⟨heq, hlt⟩
      · exact cut_step (ihs _ hlt (n + m)) rfl rfl hpop d₁ d₂
      · exact cut_step (ihh _ hlt) heq rfl hpop d₁ d₂

/-- ⭐**Cut is admissible** in the nested calculus for KB, at any node that has a formula. -/
theorem cut {Γ : List LF} {σ : Lab} (A : Form) {n m : ℕ} (hpop : Pop σ Γ)
    (d₁ : Der S n ((σ, A) :: Γ)) (d₂ : Der S m ((σ, A.neg) :: Γ)) : ∃ k, Der S k Γ :=
  cut_step (cutIH_all _ _) rfl rfl hpop d₁ d₂

/-- The B axiom `p → □◇p`, as `¬p ∨ □◇p` at the root, with B on: the `◇` at the child reads
    `p` at its parent. -/
theorem b_axiom (hB : S.B = true) (p : ℕ) :
    Der S 3 [(([] : Lab), (Form.natom p).or (.box (.dia (.atom p))))] :=
  .or (τ := []) (A := .natom p) (B := .box (.dia (.atom p))) List.mem_cons_self
    (.box (τ := []) (A := .dia (.atom p)) 0 (by simp)
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp)
      (.dia (τ := [0]) (τ' := []) (A := .atom p) List.mem_cons_self
        (.symm hB (.edge [] 0)) ⟨Form.natom p, by simp⟩
        (.ax [] p List.mem_cons_self (by simp))))

/-- The 5 axiom `◇p → □◇p`, as `□¬p ∨ □◇p` at the root, with 5 on: the `◇` at one child reads
    `p` at its sibling. -/
theorem five_axiom (hV : S.Five = true) (p : ℕ) :
    Der S 4 [(([] : Lab), (Form.box (.natom p)).or (.box (.dia (.atom p))))] :=
  .or (τ := []) (A := .box (.natom p)) (B := .box (.dia (.atom p))) List.mem_cons_self
    (.box (τ := []) (A := .natom p) 0 (by simp)
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp)
      (.box (τ := []) (A := .dia (.atom p)) 1 (by simp)
        (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp)
        (.dia (τ := [1]) (τ' := [0]) (A := .atom p) List.mem_cons_self
          (.eucl hV (.edge [] 1) (.edge [] 0)) ⟨Form.natom p, by simp⟩
          (.ax [0] p List.mem_cons_self (by simp)))))

end KBN
