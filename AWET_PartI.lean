/-
================================================================================
  Machine-checked verification of Part I of

    N. G. Hall, H. Kellerer, M. Song,
    "Asymmetric Weighted Earliness-Tardiness: Scheduling with a Nonrestrictive
     Common Due Date", arXiv:2609.16046v1 (2026), Part I (Sections 4-9).

  Claim (Theorem I.2): the decision version of AWET with positive integer data
  and the boundary nonrestrictive due date d = Σ_j p_j is strongly NP-complete;
  in particular it is unary NP-hard.

  What this file proves (no `sorry`, only the standard axioms
  propext / Classical.choice / Quot.sound -- see `#print axioms` at the end):

  * `AWET.Inst.yes_iff`            -- Lemma I.3 + Proposition I.4:
        an AWET instance has a schedule (real start times) of cost ≤ B
        iff some early set E has canonical cost Φ(E) ≤ B.
  * `AWET.RXC3.exactCover_iff_RPE` -- Lemmas I.7-I.9 (Reduction I).
  * `AWET.RXC3.reduction_iff`      -- Lemmas I.11-I.18 (Reduction II):
        X has an exact cover  ↔  X.inst has a schedule of cost ≤ X.Bnd,
        where X.inst / X.Bnd is exactly the paper's Section 8 construction.
  * `AWET.RXC3.size_bound`         -- Lemma I.19: 8n+1 jobs and every number
        (p, wᴱ, wᴸ, d, B) bounded by (n+1)^650.
  * `AWET.AWET_strong_reduction`   -- the combination (formal core of Thm I.2).
  * `AWET.Examples`                -- sanity check: the definitions reproduce the
        paper's Appendix B numbers (Tables 10 and 13), and the theorem decides both
        worked examples (B.1 yes, B.2 no).

  Not formalized (trusted, as in the paper): NP-completeness of RXC3
  (Gonzalez 1985) and the polynomial running time of the transformation
  (all definitions below are explicit, computable formulas).

  Checked with Lean 4 v4.35.0 and Mathlib (tag v4.35.0).
  To check:  put this file in a Lake project depending on Mathlib v4.35.0 and run
             `lake env lean AWET_PartI.lean`.
  Expected output: no errors, no warnings, and three `#print axioms` lines, each
  listing exactly [propext, Classical.choice, Quot.sound].

  Map of the file (labels in parentheses refer to Part I of the paper):
    §1  AWET, schedules, cost, Φ; canonical schedule; lower bound
                                                        (Def. I.1, Lemma I.3, Prop. I.4)
    §2  RXC3, prefix data, RPE                          (Defs. I.5, I.6)
    §3  the construction of Section 8.1                 (`RXC3.inst`, `RXC3.Bnd`)
    §4  arithmetic of the construction                  (Lemma I.11)
    §5  kernel field, scale separation, compression     (Lemmas I.12-I.14)
    §6  bands, main gaps, profile decomposition         ((8.6)-(8.12))
    §7  canonical objective with the anchor early
    §8  exact load-lock decomposition                   (Lemma I.15, (8.23))
    §9  global load lock and anchor gate                (Lemma I.15, (8.24), (8.25))
    §10 expansion on the coded state space              ((8.14), (8.26))
    §11 Reduction I                                     (Lemmas I.7-I.9)
    §12 master identity, residual bound, decision gap   (Lemma I.16, (8.32)-(8.34))
    §13 main theorem                                    (Lemmas I.17, I.18)
    §14 polynomial size bounds                          (Lemma I.19)
    §15 summary theorem;  §16 worked examples           (Appendix B)
================================================================================
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace AWET

/-! ## Generic pair-sum lemmas -/

section PairSum
variable {J : Type} [Fintype J] [LinearOrder J]

theorem sum_key_lt_swap {α : Type} [LinearOrder α] (key : J → α)
    (g : J → J → ℤ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, if key j < key i then g i j else 0)
      = ∑ i, ∑ j, if key i < key j then g i j else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hg]

theorem two_mul_sum_key_lt {α : Type} [LinearOrder α] (key : J → α) (hk : Function.Injective key)
    (g : J → J → ℤ) (hg : ∀ i j, g i j = g j i) :
    2 * (∑ i, ∑ j, if key j < key i then g i j else 0)
      = ∑ i, ∑ j, if i ≠ j then g i j else 0 := by
  rw [two_mul]
  conv_lhs => rhs; rw [sum_key_lt_swap key g hg]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hij : i = j
  · subst hij; simp
  · have hne : key i ≠ key j := fun h => hij (hk h)
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hij, h, not_lt.mpr h.le]
    · simp [hij, h, not_lt.mpr h.le]

/-- A pair sum taken along any strict total order (given by an injective key)
equals the pair sum along the index order, for a symmetric summand. -/
theorem sum_key_lt_eq {α : Type} [LinearOrder α] (key : J → α) (hk : Function.Injective key)
    (g : J → J → ℤ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, if key j < key i then g i j else 0)
      = ∑ i, ∑ j, if i < j then g i j else 0 := by
  have h1 := two_mul_sum_key_lt key hk g hg
  have h2 := two_mul_sum_key_lt (id : J → J) Function.injective_id g hg
  have h3 := sum_key_lt_swap (id : J → J) g hg
  simp only [id] at h2 h3
  rw [h3] at h2
  omega

end PairSum

/-! ## 1. The AWET problem -/

/-- An AWET instance: positive integer processing times and weights. -/
structure Inst (J : Type) [Fintype J] where
  p : J → ℤ
  wE : J → ℤ
  wL : J → ℤ
  hp : ∀ j, 0 < p j
  hwE : ∀ j, 0 < wE j
  hwL : ∀ j, 0 < wL j

namespace Inst
variable {J : Type} [Fintype J] [LinearOrder J]

/-- The boundary nonrestrictive common due date `d = Σ p_j`. -/
def d (I : Inst J) : ℤ := ∑ j, I.p j

/-- A feasible nonpreemptive single-machine schedule, given by (real) completion times:
nonnegative start times and no two jobs overlapping. -/
structure Sched (I : Inst J) where
  C : J → ℝ
  start_nonneg : ∀ j, (I.p j : ℝ) ≤ C j
  no_overlap : ∀ i j, i ≠ j → C i + I.p j ≤ C j ∨ C j + I.p i ≤ C i

/-- Total weighted earliness-tardiness cost. -/
def cost (I : Inst J) (σ : I.Sched) : ℝ :=
  ∑ j, ((I.wE j : ℝ) * max ((I.d : ℝ) - σ.C j) 0 + (I.wL j : ℝ) * max (σ.C j - (I.d : ℝ)) 0)

/-- Decision version: is there a feasible schedule of cost at most `B`? -/
def Yes (I : Inst J) (B : ℤ) : Prop := ∃ σ : I.Sched, I.cost σ ≤ (B : ℝ)

/-- early pair coefficient `p_i p_j min(r_i, r_j)` written without division -/
def eP (I : Inst J) (i j : J) : ℤ := min (I.p j * I.wE i) (I.p i * I.wE j)
/-- tardy pair coefficient `p_i p_j min(s_i, s_j)` -/
def tP (I : Inst J) (i j : J) : ℤ := min (I.p j * I.wL i) (I.p i * I.wL j)

/-- The canonical set objective `Φ(E)` of Proposition I.4 (equation (SO)). -/
def Φ (I : Inst J) (E : Finset J) : ℤ :=
  (∑ i, ∑ j, if i < j then
      ((if i ∈ E ∧ j ∈ E then I.eP i j else 0) + (if i ∉ E ∧ j ∉ E then I.tP i j else 0))
    else 0)
  + ∑ i, if i ∈ E then 0 else I.p i * I.wL i

theorem eP_symm (I : Inst J) (i j : J) : I.eP i j = I.eP j i := by
  unfold eP; rw [min_comm]
theorem tP_symm (I : Inst J) (i j : J) : I.tP i j = I.tP j i := by
  unfold tP; rw [min_comm]

end Inst
end AWET


open Finset

namespace AWET
namespace Inst
variable {J : Type} [Fintype J] [LinearOrder J] (I : Inst J)

/-! ### The canonical (V-shaped, due-date aligned) schedule of an early set -/

/-- Smith ratios as rationals. -/
def rE (j : J) : ℚ := (I.wE j : ℚ) / I.p j
def rL (j : J) : ℚ := (I.wL j : ℚ) / I.p j

/-- Keys: a larger key means "closer to the due date" (ties broken by the index). -/
def keyE (j : J) : ℚ ×ₗ J := toLex (I.rE j, j)
def keyL (j : J) : ℚ ×ₗ J := toLex (I.rL j, j)

theorem keyE_inj : Function.Injective I.keyE := by
  intro a b h
  have := congrArg (fun x => (ofLex x).2) h
  simpa [keyE] using this

theorem keyL_inj : Function.Injective I.keyL := by
  intro a b h
  have := congrArg (fun x => (ofLex x).2) h
  simpa [keyL] using this

theorem eP_of_keyE_lt {i j : J} (h : I.keyE i < I.keyE j) : I.eP i j = I.p j * I.wE i := by
  have hr : I.rE i ≤ I.rE j := by
    rcases (Prod.Lex.toLex_lt_toLex.mp h) with h1 | ⟨h1, _⟩
    · exact h1.le
    · exact h1.le
  have hpi : (0:ℚ) < I.p i := by exact_mod_cast I.hp i
  have hpj : (0:ℚ) < I.p j := by exact_mod_cast I.hp j
  unfold rE at hr
  rw [div_le_div_iff₀ hpi hpj] at hr
  have h2 : I.p j * I.wE i ≤ I.p i * I.wE j := by
    have h3 : ((I.p j * I.wE i : ℤ) : ℚ) ≤ ((I.p i * I.wE j : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast h3
  unfold eP; exact min_eq_left h2

theorem tP_of_keyL_lt {i j : J} (h : I.keyL i < I.keyL j) : I.tP i j = I.p j * I.wL i := by
  have hr : I.rL i ≤ I.rL j := by
    rcases (Prod.Lex.toLex_lt_toLex.mp h) with h1 | ⟨h1, _⟩
    · exact h1.le
    · exact h1.le
  have hpi : (0:ℚ) < I.p i := by exact_mod_cast I.hp i
  have hpj : (0:ℚ) < I.p j := by exact_mod_cast I.hp j
  unfold rL at hr
  rw [div_le_div_iff₀ hpi hpj] at hr
  have h2 : I.p j * I.wL i ≤ I.p i * I.wL j := by
    have h3 : ((I.p j * I.wL i : ℤ) : ℚ) ≤ ((I.p i * I.wL j : ℤ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast h3
  unfold tP; exact min_eq_left h2

theorem sum_p_nonneg (s : Finset J) : 0 ≤ ∑ i ∈ s, I.p i :=
  Finset.sum_nonneg (fun i _ => (I.hp i).le)

theorem sum_p_le_d (s : Finset J) : ∑ i ∈ s, I.p i ≤ I.d :=
  Finset.sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _ => (I.hp i).le)

theorem d_nonneg : 0 ≤ I.d := I.sum_p_nonneg univ

theorem sum_filter_mono_add {s : Finset J} {j : J} (P Q : J → Prop) [DecidablePred P]
    [DecidablePred Q] (hPQ : ∀ x ∈ s, P x → Q x) (hj : j ∈ s) (hQj : Q j) (hPj : ¬ P j) :
    ∑ i ∈ s.filter P, I.p i + I.p j ≤ ∑ i ∈ s.filter Q, I.p i := by
  have hsub : insert j (s.filter P) ⊆ s.filter Q := by
    intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact mem_filter.mpr ⟨hj, hQj⟩
    · have := mem_filter.mp hx
      exact mem_filter.mpr ⟨this.1, hPQ x this.1 this.2⟩
  have hnot : j ∉ s.filter P := by simp [hPj]
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (I.hp i).le)
  rw [Finset.sum_insert hnot] at this
  linarith

/-- Completion times of the canonical schedule of `E`: the early jobs end at `d` in
nondecreasing order of early ratio towards `d`, the tardy jobs start at `d` in nonincreasing
order of tardy ratio. -/
def canC (E : Finset J) (j : J) : ℤ :=
  if j ∈ E then I.d - ∑ i ∈ E.filter (fun i => I.keyE j < I.keyE i), I.p i
  else I.d + I.p j + ∑ i ∈ Eᶜ.filter (fun i => I.keyL j < I.keyL i), I.p i

theorem canC_mem {E : Finset J} {j : J} (hj : j ∈ E) :
    I.canC E j = I.d - ∑ i ∈ E.filter (fun i => I.keyE j < I.keyE i), I.p i := by
  simp [canC, hj]

theorem canC_nmem {E : Finset J} {j : J} (hj : j ∉ E) :
    I.canC E j = I.d + I.p j + ∑ i ∈ Eᶜ.filter (fun i => I.keyL j < I.keyL i), I.p i := by
  simp [canC, hj]

theorem canC_start (E : Finset J) (j : J) : I.p j ≤ I.canC E j := by
  by_cases hj : j ∈ E
  · rw [I.canC_mem hj]
    have h1 := I.sum_filter_mono_add (s := E) (j := j) (fun i => I.keyE j < I.keyE i)
      (fun _ => True) (fun _ _ _ => trivial) hj trivial (lt_irrefl _)
    have h2 := I.sum_p_le_d E
    simp only [Finset.filter_true] at h1
    linarith
  · rw [I.canC_nmem hj]
    have := I.d_nonneg
    have := I.sum_p_nonneg (Eᶜ.filter (fun i => I.keyL j < I.keyL i))
    linarith

theorem canC_overlap (E : Finset J) (i j : J) (hij : i ≠ j) :
    I.canC E i + I.p j ≤ I.canC E j ∨ I.canC E j + I.p i ≤ I.canC E i := by
  by_cases hi : i ∈ E <;> by_cases hj : j ∈ E
  · rw [I.canC_mem hi, I.canC_mem hj]
    have hne : I.keyE i ≠ I.keyE j := fun h => hij (I.keyE_inj h)
    rcases lt_or_gt_of_ne hne with h | h
    · left
      have := I.sum_filter_mono_add (s := E) (j := j) (fun x => I.keyE j < I.keyE x)
        (fun x => I.keyE i < I.keyE x) (fun x _ hx => lt_trans h hx) hj h (lt_irrefl _)
      linarith
    · right
      have := I.sum_filter_mono_add (s := E) (j := i) (fun x => I.keyE i < I.keyE x)
        (fun x => I.keyE j < I.keyE x) (fun x _ hx => lt_trans h hx) hi h (lt_irrefl _)
      linarith
  · left
    rw [I.canC_mem hi, I.canC_nmem hj]
    have := I.sum_p_nonneg (E.filter (fun x => I.keyE i < I.keyE x))
    have := I.sum_p_nonneg (Eᶜ.filter (fun x => I.keyL j < I.keyL x))
    linarith
  · right
    rw [I.canC_nmem hi, I.canC_mem hj]
    have := I.sum_p_nonneg (E.filter (fun x => I.keyE j < I.keyE x))
    have := I.sum_p_nonneg (Eᶜ.filter (fun x => I.keyL i < I.keyL x))
    linarith
  · have hi' : i ∈ Eᶜ := mem_compl.mpr hi
    have hj' : j ∈ Eᶜ := mem_compl.mpr hj
    rw [I.canC_nmem hi, I.canC_nmem hj]
    have hne : I.keyL i ≠ I.keyL j := fun h => hij (I.keyL_inj h)
    rcases lt_or_gt_of_ne hne with h | h
    · right
      have := I.sum_filter_mono_add (s := Eᶜ) (j := j) (fun x => I.keyL j < I.keyL x)
        (fun x => I.keyL i < I.keyL x) (fun x _ hx => lt_trans h hx) hj' h (lt_irrefl _)
      linarith
    · left
      have := I.sum_filter_mono_add (s := Eᶜ) (j := i) (fun x => I.keyL i < I.keyL x)
        (fun x => I.keyL j < I.keyL x) (fun x _ hx => lt_trans h hx) hi' h (lt_irrefl _)
      linarith

/-- The canonical schedule as a feasible schedule. -/
def canSched (E : Finset J) : I.Sched where
  C := fun j => (I.canC E j : ℝ)
  start_nonneg := fun j => by exact_mod_cast I.canC_start E j
  no_overlap := fun i j hij => by
    rcases I.canC_overlap E i j hij with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h

end Inst
end AWET

namespace AWET
namespace Inst
variable {J : Type} [Fintype J] [LinearOrder J] (I : Inst J)

/-- integer cost of the canonical schedule, written per job -/
def canCostInt (E : Finset J) : ℤ :=
  ∑ j, if j ∈ E then I.wE j * ∑ i ∈ E.filter (fun i => I.keyE j < I.keyE i), I.p i
       else I.wL j * (I.p j + ∑ i ∈ Eᶜ.filter (fun i => I.keyL j < I.keyL i), I.p i)

theorem cost_canSched_eq_int (E : Finset J) :
    I.cost (I.canSched E) = (I.canCostInt E : ℝ) := by
  unfold cost canCostInt
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show (I.wE j : ℝ) * max ((I.d : ℝ) - (I.canC E j : ℝ)) 0
      + (I.wL j : ℝ) * max ((I.canC E j : ℝ) - I.d) 0 = _
  by_cases hj : j ∈ E
  · rw [I.canC_mem hj]
    have hS := I.sum_p_nonneg (E.filter (fun i => I.keyE j < I.keyE i))
    have hS' : (0:ℝ) ≤ ((∑ i ∈ E.filter (fun i => I.keyE j < I.keyE i), I.p i : ℤ) : ℝ) := by
      exact_mod_cast hS
    simp only [hj, ite_true]
    push_cast at hS' ⊢
    rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [I.canC_nmem hj]
    have hS := I.sum_p_nonneg (Eᶜ.filter (fun i => I.keyL j < I.keyL i))
    have hp := I.hp j
    have hS' : (0:ℝ) ≤ ((∑ i ∈ Eᶜ.filter (fun i => I.keyL j < I.keyL i), I.p i : ℤ) : ℝ) := by
      exact_mod_cast hS
    have hp' : (0:ℝ) < (I.p j : ℝ) := by exact_mod_cast hp
    simp only [hj, ite_false]
    push_cast at hS' ⊢
    rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

theorem filter_eq_univ_filter (E : Finset J) (P : J → Prop) [DecidablePred P] :
    E.filter P = univ.filter (fun i => i ∈ E ∧ P i) := by
  ext i; simp

theorem early_part (E : Finset J) :
    (∑ j, if j ∈ E then I.wE j * ∑ i ∈ E.filter (fun i => I.keyE j < I.keyE i), I.p i else 0)
      = ∑ i, ∑ j, if i < j then (if i ∈ E ∧ j ∈ E then I.eP i j else 0) else 0 := by
  have h1 : (∑ j, if j ∈ E then I.wE j * ∑ i ∈ E.filter (fun i => I.keyE j < I.keyE i), I.p i
      else 0) = ∑ j, ∑ i, if I.keyE j < I.keyE i then
        (if i ∈ E ∧ j ∈ E then I.eP i j else 0) else 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j ∈ E
    · simp only [hj, ite_true]
      rw [filter_eq_univ_filter, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ E <;> by_cases hk : I.keyE j < I.keyE i <;> simp [hi, hk]
      rw [I.eP_symm, I.eP_of_keyE_lt hk]; ring
    · simp [hj]
  rw [h1, Finset.sum_comm]
  exact sum_key_lt_eq I.keyE I.keyE_inj (fun i j => if i ∈ E ∧ j ∈ E then I.eP i j else 0)
    (by intro i j; by_cases hi : i ∈ E <;> by_cases hj : j ∈ E <;> simp [hi, hj, I.eP_symm])

theorem tardy_part (E : Finset J) :
    (∑ j, if j ∈ E then 0 else
        I.wL j * ∑ i ∈ Eᶜ.filter (fun i => I.keyL j < I.keyL i), I.p i)
      = ∑ i, ∑ j, if i < j then (if i ∉ E ∧ j ∉ E then I.tP i j else 0) else 0 := by
  have h1 : (∑ j, if j ∈ E then 0 else
        I.wL j * ∑ i ∈ Eᶜ.filter (fun i => I.keyL j < I.keyL i), I.p i)
      = ∑ j, ∑ i, if I.keyL j < I.keyL i then
        (if i ∉ E ∧ j ∉ E then I.tP i j else 0) else 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j ∈ E
    · simp [hj]
    · simp only [hj, ite_false]
      rw [filter_eq_univ_filter, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ E <;> by_cases hk : I.keyL j < I.keyL i <;> simp [hi, hk]
      rw [I.tP_symm, I.tP_of_keyL_lt hk]; ring
  rw [h1, Finset.sum_comm]
  exact sum_key_lt_eq I.keyL I.keyL_inj (fun i j => if i ∉ E ∧ j ∉ E then I.tP i j else 0)
    (by intro i j; by_cases hi : i ∈ E <;> by_cases hj : j ∈ E <;> simp [hi, hj, I.tP_symm])

theorem Φ_split (E : Finset J) : I.Φ E =
    (∑ i, ∑ j, if i < j then (if i ∈ E ∧ j ∈ E then I.eP i j else 0) else 0)
    + (∑ i, ∑ j, if i < j then (if i ∉ E ∧ j ∉ E then I.tP i j else 0) else 0)
    + ∑ i, if i ∈ E then 0 else I.p i * I.wL i := by
  unfold Φ
  have h : ∀ i j : J, (if i < j then ((if i ∈ E ∧ j ∈ E then I.eP i j else 0)
      + (if i ∉ E ∧ j ∉ E then I.tP i j else 0)) else 0)
      = (if i < j then (if i ∈ E ∧ j ∈ E then I.eP i j else 0) else 0)
        + (if i < j then (if i ∉ E ∧ j ∉ E then I.tP i j else 0) else 0) := by
    intro i j; split_ifs <;> simp
  simp only [h, Finset.sum_add_distrib]

theorem canCostInt_eq_Φ (E : Finset J) : I.canCostInt E = I.Φ E := by
  have hsplit : I.canCostInt E =
      (∑ j, if j ∈ E then I.wE j * ∑ i ∈ E.filter (fun i => I.keyE j < I.keyE i), I.p i else 0)
      + (∑ j, if j ∈ E then 0 else
        I.wL j * ∑ i ∈ Eᶜ.filter (fun i => I.keyL j < I.keyL i), I.p i)
      + ∑ i, if i ∈ E then 0 else I.p i * I.wL i := by
    unfold canCostInt
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j ∈ E <;> simp [hj]; ring
  rw [hsplit, I.early_part, I.tardy_part, I.Φ_split]

/-- **Proposition I.4 (feasibility part).** Every early set `E` is realised by a feasible
schedule whose cost is exactly `Φ(E)`. -/
theorem exists_sched_cost_eq (E : Finset J) : ∃ σ : I.Sched, I.cost σ = (I.Φ E : ℝ) :=
  ⟨I.canSched E, by rw [I.cost_canSched_eq_int, I.canCostInt_eq_Φ]⟩

end Inst
end AWET


open Finset

namespace AWET
namespace Inst
variable {J : Type} [Fintype J] [LinearOrder J] {I : Inst J}

/-! ### Lower bound: every schedule costs at least `Φ(E)` for some early set `E` -/

theorem p_pos_real (I : Inst J) (j : J) : (0:ℝ) < I.p j := by exact_mod_cast I.hp j

theorem Sched.C_ne (σ : I.Sched) {i j : J} (hij : i ≠ j) : σ.C i ≠ σ.C j := by
  intro h
  have hi := I.p_pos_real i
  have hj := I.p_pos_real j
  rcases σ.no_overlap i j hij with h1 | h1 <;> linarith

theorem Sched.C_inj (σ : I.Sched) : Function.Injective σ.C := fun _ _ h =>
  by_contra (fun hij => σ.C_ne hij h)

/-- a job completing later starts after the earlier one completes -/
theorem Sched.after (σ : I.Sched) {i j : J} (h : σ.C j < σ.C i) : σ.C j + I.p i ≤ σ.C i := by
  have hij : i ≠ j := fun e => by subst e; exact lt_irrefl _ h
  have hj := I.p_pos_real j
  rcases σ.no_overlap i j hij with h1 | h1
  · linarith
  · exact h1

/-- Packing: pairwise disjoint processing intervals inside `[a, b]` have total length at most
`b - a`. -/
theorem Sched.pack (σ : I.Sched) (a : ℝ) (F : Finset J) :
    ∀ b : ℝ, a ≤ b → (∀ i ∈ F, a + I.p i ≤ σ.C i ∧ σ.C i ≤ b) →
      (∑ i ∈ F, (I.p i : ℝ)) ≤ b - a := by
  refine Finset.induction_on_max_value σ.C F ?_ ?_
  · intro b hab _; simp; linarith
  · intro x s hx hmax ih b hab hF
    have hxF := hF x (mem_insert_self x s)
    have hs : ∀ i ∈ s, a + I.p i ≤ σ.C i ∧ σ.C i ≤ σ.C x - I.p x := by
      intro i hi
      have hi' := hF i (mem_insert_of_mem hi)
      refine ⟨hi'.1, ?_⟩
      have hix : i ≠ x := fun e => hx (e ▸ hi)
      have hlt : σ.C i < σ.C x := lt_of_le_of_ne (hmax i hi) (σ.C_ne hix)
      have := σ.after hlt
      linarith
    have := ih (σ.C x - I.p x) (by linarith [hxF.1]) hs
    rw [Finset.sum_insert hx]
    linarith [hxF.2]

/-- the completion-order cost expression of an early set -/
noncomputable def ordCost (σ : I.Sched) (E : Finset J) : ℝ :=
  ∑ j, if j ∈ E then (I.wE j : ℝ) * ∑ i ∈ E.filter (fun i => σ.C j < σ.C i), (I.p i : ℝ)
       else (I.wL j : ℝ) * ((I.p j : ℝ) + ∑ i ∈ Eᶜ.filter (fun i => σ.C i < σ.C j), (I.p i : ℝ))

theorem Φ_le_ordCost (σ : I.Sched) (E : Finset J) : (I.Φ E : ℝ) ≤ ordCost σ E := by
  -- early pairs
  have hA : ((∑ i, ∑ j, if i < j then (if i ∈ E ∧ j ∈ E then I.eP i j else 0) else 0 : ℤ) : ℝ)
      ≤ ∑ j, if j ∈ E then (I.wE j : ℝ) * ∑ i ∈ E.filter (fun i => σ.C j < σ.C i), (I.p i : ℝ)
        else 0 := by
    rw [← sum_key_lt_eq σ.C σ.C_inj (fun i j => if i ∈ E ∧ j ∈ E then I.eP i j else 0)
      (by intro i j; by_cases hi : i ∈ E <;> by_cases hj : j ∈ E <;> simp [hi, hj, I.eP_symm])]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hj : j ∈ E
    · simp only [hj, ite_true]
      rw [Inst.filter_eq_univ_filter, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_le_sum (fun i _ => ?_)
      by_cases hi : i ∈ E <;> by_cases hk : σ.C j < σ.C i <;> simp [hi, hk]
      have : I.eP i j ≤ I.p i * I.wE j := min_le_right _ _
      have : ((I.eP i j : ℤ) : ℝ) ≤ ((I.p i * I.wE j : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    · simp [hj]
  -- tardy pairs
  have hB : ((∑ i, ∑ j, if i < j then (if i ∉ E ∧ j ∉ E then I.tP i j else 0) else 0 : ℤ) : ℝ)
      ≤ ∑ j, if j ∈ E then 0 else
          (I.wL j : ℝ) * ∑ i ∈ Eᶜ.filter (fun i => σ.C i < σ.C j), (I.p i : ℝ) := by
    rw [← sum_key_lt_eq σ.C σ.C_inj (fun i j => if i ∉ E ∧ j ∉ E then I.tP i j else 0)
      (by intro i j; by_cases hi : i ∈ E <;> by_cases hj : j ∈ E <;> simp [hi, hj, I.tP_symm])]
    push_cast
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hj : j ∈ E
    · simp only [hj, ite_true]
      refine Finset.sum_nonpos (fun i _ => ?_)
      by_cases hk : σ.C i < σ.C j <;> simp [hk]
    · simp only [hj, ite_false]
      rw [Inst.filter_eq_univ_filter, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_le_sum (fun i _ => ?_)
      by_cases hi : i ∈ E <;> by_cases hk : σ.C i < σ.C j <;> simp [hi, hk]
      have : I.tP j i ≤ I.p i * I.wL j := min_le_left _ _
      have : ((I.tP j i : ℤ) : ℝ) ≤ ((I.p i * I.wL j : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
  have hsplit : ordCost σ E =
      (∑ j, if j ∈ E then (I.wE j : ℝ) * ∑ i ∈ E.filter (fun i => σ.C j < σ.C i), (I.p i : ℝ)
        else 0)
      + (∑ j, if j ∈ E then 0 else
          (I.wL j : ℝ) * ∑ i ∈ Eᶜ.filter (fun i => σ.C i < σ.C j), (I.p i : ℝ))
      + ∑ i, if i ∈ E then (0:ℝ) else (I.p i : ℝ) * I.wL i := by
    unfold ordCost
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : j ∈ E <;> simp [hj]; ring
  have hΦ : (I.Φ E : ℝ) =
      ((∑ i, ∑ j, if i < j then (if i ∈ E ∧ j ∈ E then I.eP i j else 0) else 0 : ℤ) : ℝ)
      + ((∑ i, ∑ j, if i < j then (if i ∉ E ∧ j ∉ E then I.tP i j else 0) else 0 : ℤ) : ℝ)
      + ∑ i, if i ∈ E then (0:ℝ) else (I.p i : ℝ) * I.wL i := by
    rw [I.Φ_split]
    push_cast
    refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
    by_cases h : i ∈ E <;> simp [h]
  rw [hΦ, hsplit]
  linarith

end Inst
end AWET

namespace AWET
namespace Inst
variable {J : Type} [Fintype J] [LinearOrder J] {I : Inst J}

theorem sum_filter_indicator (E : Finset J) (P : J → Prop) [DecidablePred P] (f : J → ℝ) :
    ∑ i ∈ E.filter P, f i = ∑ i, if i ∈ E ∧ P i then f i else 0 := by
  rw [Inst.filter_eq_univ_filter, Finset.sum_filter]

/-- **Lemma I.3 / Proposition I.4 (optimality part).** Every feasible schedule costs at least
`Φ(E)` for some early set `E`. -/
theorem exists_Φ_le_cost (σ : I.Sched) : ∃ E : Finset J, (I.Φ E : ℝ) ≤ I.cost σ := by
  set d : ℝ := (I.d : ℝ) with hd
  set E0 : Finset J := univ.filter (fun j => σ.C j ≤ d) with hE0
  have memE0 : ∀ j, j ∈ E0 ↔ σ.C j ≤ d := by intro j; simp [hE0]
  have hA : ∀ j ∈ E0, ∑ i ∈ E0.filter (fun i => σ.C j < σ.C i), (I.p i : ℝ) ≤ d - σ.C j := by
    intro j hj
    have hjd : σ.C j ≤ d := (memE0 j).mp hj
    exact σ.pack (σ.C j) _ d hjd (fun i hi => by
      have hi' := mem_filter.mp hi
      exact ⟨σ.after hi'.2, (memE0 i).mp hi'.1⟩)
  -- per-job cost in each regime
  have hjobE : ∀ j ∈ E0, (I.wE j : ℝ) * max (d - σ.C j) 0 + (I.wL j : ℝ) * max (σ.C j - d) 0
      = (I.wE j : ℝ) * (d - σ.C j) := by
    intro j hj
    have := (memE0 j).mp hj
    rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hjobT : ∀ j ∉ E0, (I.wE j : ℝ) * max (d - σ.C j) 0 + (I.wL j : ℝ) * max (σ.C j - d) 0
      = (I.wL j : ℝ) * (σ.C j - d) := by
    intro j hj
    have : d < σ.C j := lt_of_not_ge (fun h => hj ((memE0 j).mpr h))
    rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have hwE : ∀ j, (0:ℝ) ≤ I.wE j := fun j => by exact_mod_cast (I.hwE j).le
  have hwL : ∀ j, (0:ℝ) ≤ I.wL j := fun j => by exact_mod_cast (I.hwL j).le
  by_cases hT : E0ᶜ.Nonempty
  · obtain ⟨js, hjs, hmin⟩ := Finset.exists_min_image E0ᶜ σ.C hT
    have hjs' : js ∉ E0 := mem_compl.mp hjs
    have hjs_gt : d < σ.C js := lt_of_not_ge (fun h => hjs' ((memE0 js).mpr h))
    have hpjs := I.p_pos_real js
    set θ : ℝ := d - (σ.C js - I.p js) with hθ
    set θp : ℝ := max θ 0 with hθp
    have hθp0 : 0 ≤ θp := le_max_right _ _
    have hθp_le : θp ≤ I.p js := max_le (by linarith) hpjs.le
    -- early jobs end before js starts
    have hEbefore : ∀ i ∈ E0, σ.C i ≤ σ.C js - I.p js := by
      intro i hi
      have : σ.C i < σ.C js := lt_of_le_of_lt ((memE0 i).mp hi) hjs_gt
      have := σ.after this
      linarith
    have hA' : ∀ j ∈ E0, ∑ i ∈ E0.filter (fun i => σ.C j < σ.C i), (I.p i : ℝ) + θp
        ≤ d - σ.C j := by
      intro j hj
      rcases le_total θ 0 with h | h
      · rw [hθp, max_eq_right h]; linarith [hA j hj]
      · rw [hθp, max_eq_left h]
        have := σ.pack (σ.C j) (E0.filter (fun i => σ.C j < σ.C i)) (σ.C js - I.p js)
          (hEbefore j hj) (fun i hi => by
            have hi' := mem_filter.mp hi
            exact ⟨σ.after hi'.2, hEbefore i hi'.1⟩)
        linarith
    -- tardy jobs: everything tardy up to `j` is packed in `[S_js, C_j]`
    have hB : ∀ j ∉ E0, (I.p j : ℝ) + ∑ i ∈ E0ᶜ.filter (fun i => σ.C i < σ.C j), (I.p i : ℝ)
        - θp ≤ σ.C j - d := by
      intro j hj
      have hjT : j ∈ E0ᶜ := mem_compl.mpr hj
      have hnot : j ∉ E0ᶜ.filter (fun i => σ.C i < σ.C j) := by simp
      have hpack := σ.pack (σ.C js - I.p js) (insert j (E0ᶜ.filter (fun i => σ.C i < σ.C j)))
        (σ.C j) (by linarith [hmin j hjT]) (fun i hi => by
          rw [mem_insert] at hi
          have key : ∀ i ∈ E0ᶜ, σ.C js - I.p js + I.p i ≤ σ.C i := by
            intro i hiT
            by_cases hij : i = js
            · subst hij; linarith
            · have hlt : σ.C js < σ.C i :=
                lt_of_le_of_ne (hmin i hiT) (σ.C_ne (Ne.symm hij))
              have := σ.after hlt
              linarith
          rcases hi with rfl | hi
          · exact ⟨key i hjT, le_refl _⟩
          · have hi' := mem_filter.mp hi
            exact ⟨key i hi'.1, hi'.2.le⟩)
      rw [Finset.sum_insert hnot] at hpack
      rcases le_total θ 0 with h | h
      · rw [hθp, max_eq_right h]
        have : d < σ.C j := lt_of_not_ge (fun h' => hj ((memE0 j).mpr h'))
        linarith
      · rw [hθp, max_eq_left h]; linarith
    -- the linear lower bound
    set WE : ℝ := ∑ j, if j ∈ E0 then (I.wE j : ℝ) else 0 with hWE
    set WL : ℝ := ∑ j, if j ∈ E0 then 0 else (I.wL j : ℝ) with hWL
    have hLB : ordCost σ E0 + θp * (WE - WL) ≤ I.cost σ := by
      have h1 : ordCost σ E0 + θp * (WE - WL) = ∑ j, if j ∈ E0 then
          (I.wE j : ℝ) * (∑ i ∈ E0.filter (fun i => σ.C j < σ.C i), (I.p i : ℝ) + θp)
          else (I.wL j : ℝ) * ((I.p j : ℝ) + ∑ i ∈ E0ᶜ.filter (fun i => σ.C i < σ.C j),
            (I.p i : ℝ) - θp) := by
        unfold ordCost
        rw [hWE, hWL, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j ∈ E0 <;> simp [hj] <;> ring
      rw [h1]
      unfold cost
      refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hj : j ∈ E0
      · simp only [hj, ite_true]
        rw [← hd, hjobE j hj]
        exact mul_le_mul_of_nonneg_left (hA' j hj) (hwE j)
      · simp only [hj, ite_false]
        rw [← hd, hjobT j hj]
        exact mul_le_mul_of_nonneg_left (hB j hj) (hwL j)
    by_cases hW : WL ≤ WE
    · refine ⟨E0, le_trans (Φ_le_ordCost σ E0) ?_⟩
      have : 0 ≤ θp * (WE - WL) := mul_nonneg hθp0 (by linarith)
      linarith
    · -- move the straddling job `js` to the early side
      rw [not_le] at hW
      set E1 := insert js E0 with hE1
      have hId : ordCost σ E1 = ordCost σ E0 + (I.p js : ℝ) * (WE - WL) := by
        rw [hWE, hWL, mul_sub, Finset.mul_sum, Finset.mul_sum]
        unfold ordCost
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : j ∈ E0
        · have hj1 : j ∈ E1 := mem_insert_of_mem hj
          have hjlt : σ.C j < σ.C js := lt_of_le_of_lt ((memE0 j).mp hj) hjs_gt
          simp only [hj, hj1, ite_true]
          rw [sum_filter_indicator, sum_filter_indicator]
          have : ∀ i, (if i ∈ E1 ∧ σ.C j < σ.C i then (I.p i : ℝ) else 0)
              = (if i ∈ E0 ∧ σ.C j < σ.C i then (I.p i : ℝ) else 0)
                + (if i = js then (I.p js : ℝ) else 0) := by
            intro i
            by_cases hi : i = js
            · subst hi; simp [hE1, hjs', hjlt]
            · simp [hE1, hi]
          simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
          ring
        · by_cases hjj : j = js
          · subst hjj
            have hj1 : j ∈ E1 := mem_insert_self _ _
            simp only [hj, hj1, ite_true, ite_false]
            have e1 : E1.filter (fun i => σ.C j < σ.C i) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro i hi
              rw [hE1, mem_insert] at hi
              rcases hi with rfl | hi
              · exact lt_irrefl _
              · exact not_lt.mpr (le_of_lt (lt_of_le_of_lt ((memE0 i).mp hi) hjs_gt))
            have e2 : E0ᶜ.filter (fun i => σ.C i < σ.C j) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro i hi
              exact not_lt.mpr (hmin i hi)
            rw [e1, e2]; simp; ring
          · have hj1 : j ∉ E1 := by simp [hE1, hj, hjj]
            simp only [hj, hj1, ite_false]
            have hjT : j ∈ E0ᶜ := mem_compl.mpr hj
            have hlt : σ.C js < σ.C j := lt_of_le_of_ne (hmin j hjT) (σ.C_ne (Ne.symm hjj))
            rw [sum_filter_indicator, sum_filter_indicator]
            have : ∀ i, (if i ∈ E0ᶜ ∧ σ.C i < σ.C j then (I.p i : ℝ) else 0)
                = (if i ∈ E1ᶜ ∧ σ.C i < σ.C j then (I.p i : ℝ) else 0)
                  + (if i = js then (I.p js : ℝ) else 0) := by
              intro i
              by_cases hi : i = js
              · subst hi; simp [hE1, hjs', hlt]
              · simp [hE1, hi]
            simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
            ring
      refine ⟨E1, le_trans (Φ_le_ordCost σ E1) ?_⟩
      rw [hId]
      have : (I.p js : ℝ) * (WE - WL) ≤ θp * (WE - WL) :=
        mul_le_mul_of_nonpos_right hθp_le (by linarith)
      linarith
  · -- every job is early
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    refine ⟨E0, le_trans (Φ_le_ordCost σ E0) ?_⟩
    unfold ordCost cost
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hj : j ∈ E0 := by
      by_contra h
      have : j ∈ E0ᶜ := mem_compl.mpr h
      rw [hT] at this; simp at this
    simp only [hj, ite_true]
    rw [← hd, hjobE j hj]
    exact mul_le_mul_of_nonneg_left (hA j hj) (hwE j)

/-- **Canonical reformulation (Lemma I.3 + Proposition I.4).** The AWET decision problem with
bound `B` has a yes-answer iff some early set `E` has canonical cost `Φ(E) ≤ B`. -/
theorem yes_iff (B : ℤ) : I.Yes B ↔ ∃ E : Finset J, I.Φ E ≤ B := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨E, hE⟩ := exists_Φ_le_cost σ
    exact ⟨E, by exact_mod_cast le_trans hE hσ⟩
  · rintro ⟨E, hE⟩
    obtain ⟨σ, hσ⟩ := I.exists_sched_cost_eq E
    exact ⟨σ, by rw [hσ]; exact_mod_cast hE⟩

end Inst
end AWET


open Finset

namespace AWET

/-- state jobs: block `v`, pair `h`, heavy/light flag `b` -/
abbrev SJ (n : ℕ) := Fin n × Fin 4 × Bool

/-- a fixed injective numbering of the state jobs, used for unordered pair sums -/
def encS {n : ℕ} (i : SJ n) : ℕ := 8 * i.1.val + 2 * i.2.1.val + (if i.2.2 then 1 else 0)

/-! ## 2. Restricted Exact Cover by 3-Sets (RXC3) and Regular Prefix Exactness (RPE) -/

/-- An RXC3 instance (Definition I.5): elements `0,…,n-1`, sets `S_0,…,S_{n-1}`; set `v` is
`{S v 0 < S v 1 < S v 2}` and every element lies in exactly three sets. -/
structure RXC3 where
  n : ℕ
  S : Fin n → Fin 3 → Fin n
  mono : ∀ v, S v 0 < S v 1 ∧ S v 1 < S v 2
  reg : ∀ k : Fin n, (univ.filter (fun q : Fin n × Fin 3 => S q.1 q.2 = k)).card = 3

namespace RXC3
variable (X : RXC3)

/-- `x` selects an exact cover: every element lies in exactly one selected set. -/
def IsExactCover (x : Fin X.n → Bool) : Prop :=
  ∀ k : Fin X.n, (univ.filter (fun v => x v = true ∧ ∃ h, X.S v h = k)).card = 1

def HasExactCover : Prop := ∃ x, X.IsExactCover x

/-- prefix datum `d_{v,k} = |S_v ∩ {e_1,…,e_k}|` (elements are `0,…,n-1`, so the first `k`
elements are those with index `< k`). -/
def dpre (v : Fin X.n) (k : ℕ) : ℕ := (univ.filter (fun h : Fin 3 => (X.S v h : ℕ) < k)).card

/-- prefix count `C_k(x) = Σ_v d_{v,k} x_v` -/
def Cpre (x : Fin X.n → Bool) (k : ℕ) : ℤ := ∑ v, (X.dpre v k : ℤ) * (if x v then 1 else 0)

/-- the RPE equations `C_k(x) = k` (Definition I.6) -/
def RPE (x : Fin X.n → Bool) : Prop := ∀ k, 1 ≤ k → k ≤ X.n → X.Cpre x k = k

/-! ## 3. The construction of Section 8 -/

/-- `N = n + 1` -/
def NN : ℤ := X.n + 1
def G : ℤ := X.NN ^ 20
def M : ℤ := X.NN ^ 40
def T : ℤ := X.NN ^ 50
/-- pair codes `Q_0,…,Q_3 = 10, 100, 1000, 10000` -/
def Qc (h : Fin 4) : ℤ := 10 ^ (h.val + 1)

/-- height of pair `h` of block `v`: `0` for the controller, the reversed level `κ(k) = n - k`
(0-based element `k`) for the occurrence pair of element `S v (h-1)`. -/
def ht (v : Fin X.n) (h : Fin 4) : ℕ :=
  if hh : h.val = 0 then 0 else X.n - (X.S v ⟨h.val - 1, by omega⟩ : ℕ)

/-- base processing values (8.1)-(8.2): `P_{vh} = T + M κ + Q_h` (`κ = 0` for the controller) -/
def P (v : Fin X.n) (h : Fin 4) : ℤ := X.T + X.M * X.ht v h + Qc h

/-- heavy increment: 3 for the controller pair, 1 for an occurrence pair -/
def cA (h : Fin 4) : ℤ := if h.val = 0 then 3 else 1

/-- reference sign `ε` (Table 2); `b = false` is the heavy job `A`, `b = true` the light job `B` -/
def eps (h : Fin 4) (b : Bool) : ℤ := (if h.val = 0 then -1 else 1) * (if b then -1 else 1)

/-- processing time of a state job (Table 2) -/
def pS (i : SJ X.n) : ℤ := X.P i.1 i.2.1 + (if i.2.2 then 0 else cA i.2.1)

/-- target load `β_v` -/
def β (v : Fin X.n) : ℤ := (∑ h, X.P v h) + 3

/-- `λ_v = G + n - v + 1` (1-based `v`), i.e. `G + n - v` for 0-based `v` -/
def lam (v : Fin X.n) : ℤ := X.G + X.n - (v : ℤ)
def L (v : Fin X.n) : ℤ := 2 * X.lam v
/-- minimum kernel -/
def K (u v : Fin X.n) : ℤ := min (X.L u) (X.L v)
/-- kernel field `f = K β` -/
def f (v : Fin X.n) : ℤ := ∑ u, X.K v u * X.β u

/-- early ratio (8.5) of a state job -/
def rS (i : SJ X.n) : ℤ := X.f i.1 + X.lam i.1 * X.pS i
/-- earliness weight of a state job -/
def wES (i : SJ X.n) : ℤ := X.pS i * X.rS i

/-- effective ratio of the effective atom of pair `h` of block `v` -/
def ρ (v : Fin X.n) (h : Fin 4) : ℤ := X.f v + X.lam v * (2 * X.P v h + cA h)

/-- effective atoms at height `η` -/
def atomsAt (η : ℕ) : Finset (Fin X.n × Fin 4) := univ.filter (fun a => X.ht a.1 a.2 = η)

/-- lower and upper end of the effective band at height `η` -/
def lo (η : ℕ) : ℤ :=
  if h : (X.atomsAt η).Nonempty then (X.atomsAt η).inf' h (fun a => X.ρ a.1 a.2) else 0
def hi (η : ℕ) : ℤ :=
  if h : (X.atomsAt η).Nonempty then (X.atomsAt η).sup' h (fun a => X.ρ a.1 a.2) else 0

/-- main gap above the band at height `η` -/
def gap (η : ℕ) : ℤ := X.lo (η + 1) - X.hi η
/-- the main-gap lengths `Δ_k`, `k = 1,…,n` ((8.6)-(8.7)) -/
def Δ (k : ℕ) : ℤ := X.gap (X.n - k)
/-- total band width `W` -/
def W : ℤ := ∑ η ∈ range (X.n + 1), (X.hi η - X.lo η)

/-- early pair coefficient `α_{ij} = p_i p_j min(r_i, r_j)` -/
def α (i j : SJ X.n) : ℤ := min (X.pS j * X.wES i) (X.pS i * X.wES j)

/-- baseline field `a⁰_v` (8.14); the sum over unordered pairs inside a block is written as
half the sum over ordered pairs. -/
def a0 (v : Fin X.n) : ℚ :=
  (1/8 : ℚ) * (∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
      if a ≠ b then (X.α (v, a) (v, b) : ℚ) * (eps a.1 a.2 + eps b.1 b.2) else 0)
  + (1/4 : ℚ) * ∑ a : Fin 4 × Bool, ∑ j : SJ X.n,
      if j.1 ≠ v then (X.α (v, a) j : ℚ) * eps a.1 a.2 else 0

/-- target field `a⋆_v` (8.15) -/
def astar (v : Fin X.n) : ℚ :=
  (1/4 : ℚ) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * k * X.dpre v k

/-- signed square-processing moment `D_v` -/
def Dv (v : Fin X.n) : ℤ := ∑ a : Fin 4 × Bool, eps a.1 a.2 * X.pS (v, a) ^ 2

/-- tardiness offsets (8.17) -/
def eta (v : Fin X.n) : ℤ := round ((4 * (X.a0 v - X.astar v)) / (X.Dv v : ℚ))

/-- field error (8.18) -/
def ev (v : Fin X.n) : ℚ := X.a0 v - (X.eta v : ℚ) * X.Dv v / 4 - X.astar v

def etabar (i j : SJ X.n) : ℤ := if i.1 = j.1 then X.eta i.1 else X.eta (max i.1 j.1)

/-- the oscillation budget `U` (8.21) -/
def U : ℤ :=
  1 + (∑ i : SJ X.n, ∑ j : SJ X.n, if encS i < encS j then X.α i j else 0)
    + (∑ i : SJ X.n, |X.eta i.1| * X.pS i ^ 2)
    + (∑ i : SJ X.n, ∑ j : SJ X.n,
        if encS i < encS j then |X.etabar i j| * X.pS i * X.pS j else 0)

/-- `max_v |η_v|` -/
def etamax : ℤ := ((univ.sup (fun v : Fin X.n => (X.eta v).natAbs) : ℕ) : ℤ)

/-- load-lock scale (8.22) -/
def H : ℤ := X.U + 2 * X.etamax + 2

/-- tardiness ratio (8.20) and weight of a state job -/
def sS (i : SJ X.n) : ℤ := X.H * X.L i.1 + X.eta i.1
def wLS (i : SJ X.n) : ℤ := X.pS i * X.sS i

/-- `max_i r_i` over state jobs -/
def rmax : ℤ := ((univ.sup (fun i : SJ X.n => (X.rS i).toNat) : ℕ) : ℤ)

end RXC3

/-! ### The job type: `none` is the anchor, `some i` the state job `i` -/

def Job (n : ℕ) : Type := Option (SJ n)

namespace Job
variable {n : ℕ}
instance : Fintype (Job n) := inferInstanceAs (Fintype (Option (SJ n)))
def enc : Job n → ℕ
  | none => 0
  | some i => 1 + encS i
theorem encS_inj : Function.Injective (@encS n) := by
  rintro ⟨v, h, b⟩ ⟨v', h', b'⟩ e
  simp only [encS] at e
  have hh := h.isLt; have hh' := h'.isLt
  have hv : v = v' := by
    apply Fin.ext; cases b <;> cases b' <;> simp at e <;> omega
  have hh2 : h = h' := by
    apply Fin.ext; cases b <;> cases b' <;> simp at e <;> omega
  have hb : b = b' := by
    cases b <;> cases b' <;> simp at e <;> first | rfl | omega
  rw [hv, hh2, hb]
theorem enc_inj : Function.Injective (@enc n) := by
  rintro (_ | i) (_ | j) e
  · rfl
  · simp only [enc] at e; omega
  · simp only [enc] at e; omega
  · simp only [enc] at e
    have : encS i = encS j := by omega
    rw [encS_inj this]
instance : LinearOrder (Job n) := LinearOrder.lift' enc enc_inj
def anchor : Job n := (none : Option (SJ n))
def st (i : SJ n) : Job n := (some i : Option (SJ n))
end Job

end AWET

namespace AWET

namespace Job
variable {n : ℕ}
def elim {α : Type} (j : Job n) (a : α) (g : SJ n → α) : α := Option.elim j a g
@[simp] theorem elim_anchor {α : Type} (a : α) (g : SJ n → α) : (anchor : Job n).elim a g = a := rfl
@[simp] theorem elim_st {α : Type} (i : SJ n) (a : α) (g : SJ n → α) : (st i).elim a g = g i := rfl

theorem sum_job {β : Type} [AddCommMonoid β] (F : Job n → β) :
    ∑ j : Job n, F j = F anchor + ∑ i : SJ n, F (st i) :=
  Fintype.sum_option (α := SJ n) F

theorem anchor_lt_st (i : SJ n) : (anchor : Job n) < st i := by
  show enc (anchor : Job n) < enc (st i)
  simp [enc, anchor, st]

theorem st_lt_st (i j : SJ n) : (st i : Job n) < st j ↔ encS i < encS j := by
  show enc (st i : Job n) < enc (st j) ↔ _
  simp [enc, st]

theorem st_ne_anchor (i : SJ n) : (st i : Job n) ≠ anchor := by
  intro h; cases h

theorem st_inj {i j : SJ n} (h : (st i : Job n) = st j) : i = j := Option.some.inj h

theorem cases (j : Job n) : j = anchor ∨ ∃ i, j = st i := by
  rcases j with _ | i
  · left; rfl
  · right; exact ⟨i, rfl⟩
end Job

namespace Inst
variable {J : Type} [Fintype J] [LinearOrder J] (I : Inst J)

theorem eP_pos (i j : J) : 0 < I.eP i j := by
  unfold eP; have := I.hp i; have := I.hp j; have := I.hwE i; have := I.hwE j
  exact lt_min (by positivity) (by positivity)

theorem tP_pos (i j : J) : 0 < I.tP i j := by
  unfold tP; have := I.hp i; have := I.hp j; have := I.hwL i; have := I.hwL j
  exact lt_min (by positivity) (by positivity)

theorem Φ_nonneg (E : Finset J) : 0 ≤ I.Φ E := by
  rw [Φ_split]
  have h1 : 0 ≤ ∑ i, ∑ j, (if i < j then (if i ∈ E ∧ j ∈ E then I.eP i j else 0) else 0) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      split_ifs <;> first | exact le_refl 0 | exact (I.eP_pos i j).le))
  have h2 : 0 ≤ ∑ i, ∑ j, (if i < j then (if i ∉ E ∧ j ∉ E then I.tP i j else 0) else 0) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      split_ifs <;> first | exact le_refl 0 | exact (I.tP_pos i j).le))
  have h3 : 0 ≤ ∑ i, (if i ∈ E then 0 else I.p i * I.wL i) :=
    Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact le_refl 0
      · have := I.hp i; have := I.hwL i; positivity)
  linarith

end Inst

namespace RXC3
variable (X : RXC3)

/-! ### positivity of the constructed data -/

theorem NN_pos : 0 < X.NN := by unfold NN; positivity
theorem G_pos : 0 < X.G := by unfold G; have := X.NN_pos; positivity
theorem M_pos : 0 < X.M := by unfold M; have := X.NN_pos; positivity
theorem T_pos : 0 < X.T := by unfold T; have := X.NN_pos; positivity
theorem Qc_pos (h : Fin 4) : 0 < Qc h := by unfold Qc; positivity
theorem cA_pos (h : Fin 4) : 0 < cA h := by unfold cA; split_ifs <;> norm_num
theorem P_pos (v : Fin X.n) (h : Fin 4) : 0 < X.P v h := by
  unfold P; have := X.T_pos; have := X.M_pos; have := Qc_pos h
  have : (0:ℤ) ≤ (X.ht v h : ℤ) := by positivity
  nlinarith
theorem pS_pos (i : SJ X.n) : 0 < X.pS i := by
  unfold pS; have := X.P_pos i.1 i.2.1; have := cA_pos i.2.1
  split_ifs <;> linarith
theorem β_pos (v : Fin X.n) : 0 < X.β v := by
  unfold β; have : 0 ≤ ∑ h, X.P v h := Finset.sum_nonneg (fun h _ => (X.P_pos v h).le)
  linarith
theorem lam_pos (v : Fin X.n) : 0 < X.lam v := by
  unfold lam; have := X.G_pos; have : (v : ℤ) < X.n := by exact_mod_cast v.isLt
  linarith
theorem L_pos (v : Fin X.n) : 0 < X.L v := by unfold L; have := X.lam_pos v; linarith
theorem K_pos (u v : Fin X.n) : 0 < X.K u v := lt_min (X.L_pos u) (X.L_pos v)
theorem f_nonneg (v : Fin X.n) : 0 ≤ X.f v :=
  Finset.sum_nonneg (fun u _ => (mul_pos (X.K_pos v u) (X.β_pos u)).le)
theorem rS_pos (i : SJ X.n) : 0 < X.rS i := by
  unfold rS; have := X.f_nonneg i.1; have := X.lam_pos i.1; have := X.pS_pos i
  nlinarith
theorem wES_pos (i : SJ X.n) : 0 < X.wES i := mul_pos (X.pS_pos i) (X.rS_pos i)
theorem α_pos (i j : SJ X.n) : 0 < X.α i j := by
  unfold α; have := X.pS_pos i; have := X.pS_pos j; have := X.wES_pos i; have := X.wES_pos j
  exact lt_min (by positivity) (by positivity)

theorem etamax_nonneg : 0 ≤ X.etamax := by unfold etamax; positivity
theorem abs_eta_le_etamax (v : Fin X.n) : |X.eta v| ≤ X.etamax := by
  unfold etamax
  have : (X.eta v).natAbs ≤ univ.sup (fun v : Fin X.n => (X.eta v).natAbs) :=
    Finset.le_sup (f := fun v : Fin X.n => (X.eta v).natAbs) (mem_univ v)
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

theorem U_ge_one : 1 ≤ X.U := by
  unfold U
  have h1 : 0 ≤ ∑ i : SJ X.n, ∑ j : SJ X.n, (if encS i < encS j then X.α i j else 0) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      split_ifs
      · exact (X.α_pos i j).le
      · exact le_refl 0))
  have h2 : 0 ≤ ∑ i : SJ X.n, |X.eta i.1| * X.pS i ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h3 : 0 ≤ ∑ i : SJ X.n, ∑ j : SJ X.n,
      (if encS i < encS j then |X.etabar i j| * X.pS i * X.pS j else 0) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
      split_ifs
      · have := X.pS_pos i; have := X.pS_pos j; positivity
      · exact le_refl 0))
  linarith

theorem H_pos : 0 < X.H := by unfold H; have := X.U_ge_one; have := X.etamax_nonneg; linarith
theorem H_gt_etamax : X.etamax < X.H := by
  unfold H; have := X.U_ge_one; have := X.etamax_nonneg; linarith

theorem sS_pos (i : SJ X.n) : 0 < X.sS i := by
  unfold sS
  have h1 := X.abs_eta_le_etamax i.1
  have h2 := X.H_gt_etamax
  have h3 : 2 ≤ X.L i.1 := by unfold L; have := X.lam_pos i.1; linarith
  have h4 : 2 * X.H ≤ X.H * X.L i.1 := by nlinarith [X.H_pos]
  have := neg_abs_le (X.eta i.1)
  have := X.etamax_nonneg
  linarith
theorem wLS_pos (i : SJ X.n) : 0 < X.wLS i := mul_pos (X.pS_pos i) (X.sS_pos i)
theorem rmax_nonneg : 0 ≤ X.rmax := by unfold rmax; positivity
theorem rS_le_rmax (i : SJ X.n) : X.rS i ≤ X.rmax := by
  unfold rmax
  have : (X.rS i).toNat ≤ univ.sup (fun i : SJ X.n => (X.rS i).toNat) :=
    Finset.le_sup (f := fun i : SJ X.n => (X.rS i).toNat) (mem_univ i)
  have h2 : ((X.rS i).toNat : ℤ) = X.rS i := Int.toNat_of_nonneg (X.rS_pos i).le
  rw [← h2]; exact_mod_cast this

/-! ### the AWET instance -/

/-- job data shared by the preliminary and final instances -/
def pJ (j : Job X.n) : ℤ := j.elim X.H X.pS
def wEJ (j : Job X.n) : ℤ := j.elim (X.H * (1 + X.rmax)) X.wES
theorem pJ_pos (j : Job X.n) : 0 < X.pJ j := by
  rcases Job.cases j with rfl | ⟨i, rfl⟩
  · simp [pJ, X.H_pos]
  · simp [pJ, X.pS_pos i]
theorem wEJ_pos (j : Job X.n) : 0 < X.wEJ j := by
  rcases Job.cases j with rfl | ⟨i, rfl⟩
  · simp only [wEJ, Job.elim_anchor]; have := X.H_pos; have := X.rmax_nonneg; positivity
  · simp [wEJ, X.wES_pos i]

/-- preliminary instance: the anchor's tardiness weight is a placeholder (it is irrelevant
while the anchor is early). -/
def preInst : Inst (Job X.n) where
  p := X.pJ
  wE := X.wEJ
  wL := fun j => j.elim 1 X.wLS
  hp := X.pJ_pos
  hwE := X.wEJ_pos
  hwL := fun j => by
    rcases Job.cases j with rfl | ⟨i, rfl⟩
    · simp
    · simp [X.wLS_pos i]

/-- `±1` from a Boolean spin -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- the coded early set of a spin vector: the anchor and every state job with `σ_v ε_i = +1` -/
def codedE (σ : Fin X.n → Bool) : Finset (Job X.n) :=
  univ.filter (fun j => j.elim true (fun i => decide (sgn (σ i.1) * eps i.2.1 i.2.2 = 1)) = true)

/-- the benchmark cost `C⋆` of the coded assignment `σ ≡ +1` with the anchor early -/
def Cstar : ℤ := X.preInst.Φ (X.codedE (fun _ => true))

/-- anchor tardiness ratio (8.25) -/
def sa : ℤ := 1 + ⌈(X.Cstar : ℚ) / (X.H : ℚ) ^ 2⌉

theorem Cstar_nonneg : 0 ≤ X.Cstar := Inst.Φ_nonneg _ _
theorem sa_pos : 0 < X.sa := by
  unfold sa
  have : (0:ℚ) ≤ (X.Cstar : ℚ) / (X.H : ℚ) ^ 2 := by
    have := X.Cstar_nonneg; have := X.H_pos; positivity
  have : 0 ≤ ⌈(X.Cstar : ℚ) / (X.H : ℚ) ^ 2⌉ := Int.ceil_nonneg this
  linarith

/-- **The constructed AWET instance** (Section 8.1): `8n` state jobs and one anchor. -/
def inst : Inst (Job X.n) where
  p := X.pJ
  wE := X.wEJ
  wL := fun j => j.elim (X.H * X.sa) X.wLS
  hp := X.pJ_pos
  hwE := X.wEJ_pos
  hwL := fun j => by
    rcases Job.cases j with rfl | ⟨i, rfl⟩
    · simp only [Job.elim_anchor]; exact mul_pos X.H_pos X.sa_pos
    · simp [X.wLS_pos i]

/-- residual budget `Γ` (8.32) -/
def Gam : ℚ := (9/8 : ℚ) * (X.n : ℚ) ^ 2 * X.W + (1/8 : ℚ) * ∑ v, (X.Dv v : ℚ)

/-- cross-block coupling `J_{uv}` (8.10) -/
def Jc (u v : Fin X.n) : ℚ :=
  (1/4 : ℚ) * ∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
    (eps a.1 a.2 : ℚ) * eps b.1 b.2 * X.α (u, a) (v, b)

/-- the constant coefficient `C₀` of (8.26), read off from the benchmark assignment `σ ≡ +1` -/
def C0 : ℚ := X.Cstar - ∑ v, (X.astar v + X.ev v) - ∑ u, ∑ v, if u < v then X.Jc u v else 0

/-- the constant `A` (8.29) -/
def Aconst : ℚ := X.C0 - (1/8 : ℚ) * ∑ k ∈ Icc 1 X.n,
    (X.Δ k : ℚ) * ((k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2)

/-- **The decision bound** `B = ⌊A + Γ⌋` (8.34). -/
def Bnd : ℤ := ⌊X.Aconst + X.Gam⌋

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 4. Basic arithmetic of the construction -/

theorem S_inj (v : Fin X.n) : Function.Injective (X.S v) := by
  have h := X.mono v
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all <;> omega

theorem S_lt (v : Fin X.n) (h : Fin 3) : (X.S v h : ℕ) < X.n := (X.S v h).isLt

theorem n_ge_three (hn : 0 < X.n) : 3 ≤ X.n := by
  have h := X.mono ⟨0, hn⟩
  have h2 := (X.S ⟨0, hn⟩ 2).isLt
  have : (X.S ⟨0, hn⟩ 0 : ℕ) < X.S ⟨0, hn⟩ 1 := h.1
  have : (X.S ⟨0, hn⟩ 1 : ℕ) < X.S ⟨0, hn⟩ 2 := h.2
  omega

/-! ### scales -/

section scales
variable {X}
variable (hn : 0 < X.n)
include hn

theorem NN_ge_four : 4 ≤ X.NN := by
  have := X.n_ge_three hn; unfold NN; omega

theorem n_lt_NN : (X.n : ℤ) < X.NN := by unfold NN; omega

/-- `c * N^a ≤ N^(a+k)` whenever `c ≤ 4^k` -/
theorem mul_pow_le (c : ℤ) (a k : ℕ) (hc : c ≤ 4 ^ k) : c * X.NN ^ a ≤ X.NN ^ (a + k) := by
  have h4 := NN_ge_four hn
  have hpa : 0 ≤ X.NN ^ a := by positivity
  have hk : (4:ℤ) ^ k ≤ X.NN ^ k := pow_le_pow_left₀ (by norm_num) h4 k
  rw [pow_add]
  calc c * X.NN ^ a ≤ 4 ^ k * X.NN ^ a := by
        rcases le_or_gt 0 c with h | h
        · exact mul_le_mul_of_nonneg_right hc hpa
        · nlinarith [pow_pos (show (0:ℤ) < 4 by norm_num) k]
    _ ≤ X.NN ^ k * X.NN ^ a := mul_le_mul_of_nonneg_right hk hpa
    _ = X.NN ^ a * X.NN ^ k := by ring

theorem pow_mono {a b : ℕ} (hab : a ≤ b) : X.NN ^ a ≤ X.NN ^ b :=
  pow_le_pow_right₀ (by linarith [NN_ge_four hn]) hab

theorem pow_pos' (a : ℕ) : 0 < X.NN ^ a := pow_pos (by linarith [NN_ge_four hn]) a

theorem n_le_NN : (X.n : ℤ) ≤ X.NN := (n_lt_NN hn).le

end scales

theorem G_eq : X.G = X.NN ^ 20 := rfl
theorem M_eq : X.M = X.NN ^ 40 := rfl
theorem T_eq : X.T = X.NN ^ 50 := rfl

/-! ### heights -/

theorem ht_zero (v : Fin X.n) : X.ht v 0 = 0 := by simp [ht]

theorem ht_one (v : Fin X.n) : X.ht v 1 = X.n - (X.S v 0 : ℕ) := by simp [ht]
theorem ht_two (v : Fin X.n) : X.ht v 2 = X.n - (X.S v 1 : ℕ) := by simp [ht]
theorem ht_three (v : Fin X.n) : X.ht v 3 = X.n - (X.S v 2 : ℕ) := by simp [ht]

theorem ht_le (v : Fin X.n) (h : Fin 4) : X.ht v h ≤ X.n := by
  unfold ht; split_ifs <;> omega

theorem ht_pos (v : Fin X.n) (h : Fin 4) (hh : h ≠ 0) : 1 ≤ X.ht v h := by
  unfold ht
  have : h.val ≠ 0 := fun e => hh (Fin.ext e)
  rw [dite_eq_right this]
  have := (X.S v ⟨h.val - 1, by omega⟩).isLt
  omega

theorem ht_eq_zero_iff (v : Fin X.n) (h : Fin 4) : X.ht v h = 0 ↔ h = 0 := by
  constructor
  · intro e; by_contra hh; have := X.ht_pos v h hh; omega
  · rintro rfl; exact X.ht_zero v

/-- the three occurrence heights of a block are strictly decreasing -/
theorem ht_strict (v : Fin X.n) : X.ht v 2 < X.ht v 1 ∧ X.ht v 3 < X.ht v 2 := by
  rw [ht_one, ht_two, ht_three]
  have h := X.mono v
  have h0 : (X.S v 0 : ℕ) < X.S v 1 := h.1
  have h1 : (X.S v 1 : ℕ) < X.S v 2 := h.2
  have := (X.S v 2).isLt
  omega

theorem ht_inj (v : Fin X.n) {g h : Fin 4} (e : X.ht v g = X.ht v h) : g = h := by
  have hs := X.ht_strict v
  have h0 := X.ht_zero v
  have p1 := X.ht_pos v 1 (by decide)
  have p2 := X.ht_pos v 2 (by decide)
  have p3 := X.ht_pos v 3 (by decide)
  fin_cases g <;> fin_cases h <;> simp_all <;> omega

/-! ### block arithmetic -/

theorem sum_slot {β : Type} [AddCommMonoid β] (F : Fin 4 × Bool → β) :
    ∑ a : Fin 4 × Bool, F a = ∑ h : Fin 4, (F (h, false) + F (h, true)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem eps_sq (h : Fin 4) (b : Bool) : eps h b ^ 2 = 1 := by
  unfold eps; split_ifs <;> norm_num

theorem eps_cases (h : Fin 4) (b : Bool) : eps h b = 1 ∨ eps h b = -1 := by
  unfold eps; split_ifs <;> norm_num

/-- total processing of a block is `2 β_v` -/
theorem sum_pS (v : Fin X.n) : ∑ a : Fin 4 × Bool, X.pS (v, a) = 2 * X.β v := by
  rw [sum_slot]
  simp only [pS, β, Bool.false_eq_true, ite_false, ite_true]
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp [cA]
  ring

/-- the reference orientation has zero signed load -/
theorem sum_eps_pS (v : Fin X.n) : ∑ a : Fin 4 × Bool, eps a.1 a.2 * X.pS (v, a) = 0 := by
  rw [sum_slot]
  simp only [pS, eps, Bool.false_eq_true, ite_false, ite_true]
  rw [Fin.sum_univ_four]
  simp [cA]

/-- signed mass of the effective atom of pair `h` -/
def mass (h : Fin 4) : ℤ := if h.val = 0 then -3 else 1

theorem sum_eps_pS_pair (v : Fin X.n) (h : Fin 4) :
    eps h false * X.pS (v, h, false) + eps h true * X.pS (v, h, true) = mass h := by
  simp only [pS, eps, mass, cA, Bool.false_eq_true, ite_false, ite_true]
  split_ifs <;> ring

theorem sum_eps_pS2_pair (v : Fin X.n) (h : Fin 4) :
    eps h false * X.pS (v, h, false) ^ 2 + eps h true * X.pS (v, h, true) ^ 2
      = mass h * (2 * X.P v h + cA h) := by
  simp only [pS, eps, mass, cA, Bool.false_eq_true, ite_false, ite_true]
  split_ifs <;> ring

theorem sum_mass : ∑ h : Fin 4, mass h = 0 := by
  rw [Fin.sum_univ_four]; simp [mass]

theorem Dv_eq (v : Fin X.n) : X.Dv v = ∑ h : Fin 4, mass h * (2 * X.P v h + cA h) := by
  unfold Dv; rw [sum_slot]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  exact X.sum_eps_pS2_pair v h

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ### Lemma I.11: the two zero-load states -/

/-- the digit-decoding step of Lemma I.11 -/
theorem digit_decode (T M U Z Qs res B : ℤ) (hM0 : 0 ≤ M) (hT : B * M + 11113 < T)
    (hM : 11113 < M) (hU : U ≠ 0 → 1 ≤ |U|) (hZ : |Z| ≤ B) (hQ : |Qs| ≤ 11110) (hres : |res| ≤ 3)
    (heq : T * U + M * Z + Qs + res = 0) : U = 0 ∧ Z = 0 ∧ Qs + res = 0 := by
  have hMZ : |M * Z| ≤ B * M := by
    rw [abs_mul, abs_of_nonneg hM0]; nlinarith [abs_nonneg Z]
  have hU0 : U = 0 := by
    by_contra hne
    have h1 := hU hne
    have hT0 : 0 ≤ T := by nlinarith [abs_nonneg Z]
    have hTU : T ≤ |T * U| := by rw [abs_mul, abs_of_nonneg hT0]; nlinarith
    have : T * U = -(M * Z + Qs + res) := by linarith
    rw [this, abs_neg] at hTU
    have := abs_add_three (M * Z) Qs res
    linarith
  subst hU0
  have hZ0 : Z = 0 := by
    by_contra hne
    have h1 : 1 ≤ |Z| := Int.one_le_abs hne
    have hMZ' : M ≤ |M * Z| := by rw [abs_mul, abs_of_nonneg hM0]; nlinarith
    have : M * Z = -(Qs + res) := by linarith
    rw [this, abs_neg] at hMZ'
    have := abs_add_le Qs res
    linarith
  subst hZ0
  refine ⟨rfl, rfl, by linarith⟩

theorem sgn_cases (s : Bool) : sgn s = 1 ∨ sgn s = -1 := by cases s <;> simp [sgn]

/-- the pair-code decoding step (superincreasing codes `10,100,1000,10000`) -/
theorem pair_decode (a0 a1 b0 b1 c0 c1 d0 d1 : ℤ) (ha0 : 0 ≤ a0 ∧ a0 ≤ 1) (ha1 : 0 ≤ a1 ∧ a1 ≤ 1)
    (hb0 : 0 ≤ b0 ∧ b0 ≤ 1) (hb1 : 0 ≤ b1 ∧ b1 ≤ 1) (hc0 : 0 ≤ c0 ∧ c0 ≤ 1)
    (hc1 : 0 ≤ c1 ∧ c1 ≤ 1) (hd0 : 0 ≤ d0 ∧ d0 ≤ 1) (hd1 : 0 ≤ d1 ∧ d1 ≤ 1)
    (h : 10 * (a0 + a1 - 1) + 100 * (b0 + b1 - 1) + 1000 * (c0 + c1 - 1) + 10000 * (d0 + d1 - 1)
      + (3 * a0 + b0 + c0 + d0 - 3) = 0) :
    (a0 = 1 ∧ b0 = 0 ∧ c0 = 0 ∧ d0 = 0 ∧ a1 = 0 ∧ b1 = 1 ∧ c1 = 1 ∧ d1 = 1) ∨
    (a0 = 0 ∧ b0 = 1 ∧ c0 = 1 ∧ d0 = 1 ∧ a1 = 1 ∧ b1 = 0 ∧ c1 = 0 ∧ d1 = 0) := by
  rcases (show a0 = 0 ∨ a0 = 1 by omega) with rfl | rfl <;>
  rcases (show a1 = 0 ∨ a1 = 1 by omega) with rfl | rfl <;>
  rcases (show b0 = 0 ∨ b0 = 1 by omega) with rfl | rfl <;>
  rcases (show b1 = 0 ∨ b1 = 1 by omega) with rfl | rfl <;>
  rcases (show c0 = 0 ∨ c0 = 1 by omega) with rfl | rfl <;>
  rcases (show c1 = 0 ∨ c1 = 1 by omega) with rfl | rfl <;>
  rcases (show d0 = 0 ∨ d0 = 1 by omega) with rfl | rfl <;>
  rcases (show d1 = 0 ∨ d1 = 1 by omega) with rfl | rfl <;>
  omega

/-- **Lemma I.11.** A block whose tardy processing equals `β_v` is in one of the two coded
orientations. -/
theorem two_states (hn : 0 < X.n) (v : Fin X.n) (early : Fin 4 × Bool → Bool)
    (hb : ∑ a, (if early a then 0 else X.pS (v, a)) = X.β v) :
    ∃ s : Bool, ∀ a, early a = decide (sgn s * eps a.1 a.2 = 1) := by
  -- tardy indicators
  have yd : ∀ a : Fin 4 × Bool, ∃ y : ℤ, (y = 0 ∧ early a = true) ∨ (y = 1 ∧ early a = false) := by
    intro a; cases h : early a
    · exact ⟨1, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
  choose y hy using yd
  have hb' : ∑ h : Fin 4, (y (h, false) * (X.P v h + cA h) + y (h, true) * X.P v h) = X.β v := by
    rw [← hb, sum_slot]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [pS, Bool.false_eq_true, ite_false, ite_true]
    rcases hy (h, false) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hy (h, true) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      simp [a1, a2, b1, b2]
  simp only [Fin.sum_univ_four, β, P, ht_zero, cA, Qc] at hb'
  norm_num at hb'
  have hr : ∀ a, 0 ≤ y a ∧ y a ≤ 1 := by
    intro a; rcases hy a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have h1b : (0:ℤ) ≤ (X.ht v 1 : ℤ) ∧ (X.ht v 1 : ℤ) ≤ X.n :=
    ⟨by positivity, by exact_mod_cast X.ht_le v 1⟩
  have h2b : (0:ℤ) ≤ (X.ht v 2 : ℤ) ∧ (X.ht v 2 : ℤ) ≤ X.n :=
    ⟨by positivity, by exact_mod_cast X.ht_le v 2⟩
  have h3b : (0:ℤ) ≤ (X.ht v 3 : ℤ) ∧ (X.ht v 3 : ℤ) ≤ X.n :=
    ⟨by positivity, by exact_mod_cast X.ht_le v 3⟩
  -- abbreviations
  set T := X.T with hT
  set M := X.M with hM
  set h1 : ℤ := (X.ht v 1 : ℤ)
  set h2 : ℤ := (X.ht v 2 : ℤ)
  set h3 : ℤ := (X.ht v 3 : ℤ)
  set u0 := y (0, false) + y (0, true) - 1 with hu0
  set u1 := y (1, false) + y (1, true) - 1 with hu1
  set u2 := y (2, false) + y (2, true) - 1 with hu2
  set u3 := y (3, false) + y (3, true) - 1 with hu3
  have hu : ∀ u : ℤ, -1 ≤ u → u ≤ 1 → ∀ x : ℤ, 0 ≤ x → |u * x| ≤ x := by
    intro u hl hu x hx
    rw [abs_mul, abs_of_nonneg hx]
    have : |u| ≤ 1 := abs_le.mpr ⟨hl, hu⟩
    nlinarith [abs_nonneg u]
  have r0 := hr (0, false); have r0' := hr (0, true)
  have r1 := hr (1, false); have r1' := hr (1, true)
  have r2 := hr (2, false); have r2' := hr (2, true)
  have r3 := hr (3, false); have r3' := hr (3, true)
  have hZ : |u1 * h1 + u2 * h2 + u3 * h3| ≤ 3 * X.n := by
    have a1 := hu u1 (by omega) (by omega) h1 h1b.1
    have a2 := hu u2 (by omega) (by omega) h2 h2b.1
    have a3 := hu u3 (by omega) (by omega) h3 h3b.1
    have := abs_add_three (u1 * h1) (u2 * h2) (u3 * h3)
    linarith [h1b.2, h2b.2, h3b.2]
  have hQ : |10 * u0 + 100 * u1 + 1000 * u2 + 10000 * u3| ≤ 11110 := by
    rw [abs_le]; constructor <;> omega
  have hres : |3 * y (0, false) + y (1, false) + y (2, false) + y (3, false) - 3| ≤ 3 := by
    rw [abs_le]; constructor <;> omega
  have hUne : (u0 + u1 + u2 + u3) ≠ 0 → 1 ≤ |u0 + u1 + u2 + u3| := fun h => Int.one_le_abs h
  have hscale1 : 3 * (X.n : ℤ) * M + 11113 < T := by
    have hnN := n_lt_NN hn
    have hMp : 0 < M := X.M_pos
    have e1 : 3 * (X.n : ℤ) * M ≤ 3 * (X.NN * X.NN ^ 40) := by
      have : (X.n : ℤ) * M ≤ X.NN * X.NN ^ 40 := mul_le_mul_of_nonneg_right hnN.le hMp.le
      linarith
    have e2 : 3 * (X.NN * X.NN ^ 40) ≤ X.NN ^ 49 := by
      have := mul_pow_le hn 3 41 8 (by norm_num)
      have e : X.NN * X.NN ^ 40 = X.NN ^ 41 := by ring
      rw [e]; simpa using this
    have e3 : (11113 : ℤ) < X.NN ^ 49 := by
      have := mul_pow_le hn 11114 0 7 (by norm_num)
      simp only [pow_zero, mul_one, zero_add] at this
      linarith [pow_mono hn (show 7 ≤ 49 by norm_num)]
    have e4 : 2 * X.NN ^ 49 ≤ X.NN ^ 50 := by
      have := mul_pow_le hn 2 49 1 (by norm_num); simpa using this
    have e5 : 0 < X.NN ^ 49 := pow_pos' hn 49
    rw [hT, T_eq]
    linarith
  have hscale2 : (11113 : ℤ) < M := by
    have := mul_pow_le hn 11114 0 7 (by norm_num)
    simp only [pow_zero, mul_one, zero_add] at this
    have h5 : X.NN ^ 7 < X.NN ^ 40 :=
      pow_lt_pow_right₀ (by linarith [NN_ge_four hn]) (by norm_num)
    rw [hM, M_eq]
    linarith
  have heq : T * (u0 + u1 + u2 + u3) + M * (u1 * h1 + u2 * h2 + u3 * h3)
      + (10 * u0 + 100 * u1 + 1000 * u2 + 10000 * u3)
      + (3 * y (0, false) + y (1, false) + y (2, false) + y (3, false) - 3) = 0 := by
    simp only [hu0, hu1, hu2, hu3]; linear_combination hb'
  obtain ⟨_, _, hQr⟩ := digit_decode T M _ _ _ _ (3 * X.n) X.M_pos.le hscale1 hscale2 hUne
    hZ hQ hres heq
  simp only [hu0, hu1, hu2, hu3] at hQr
  have key := pair_decode (y (0, false)) (y (0, true)) (y (1, false)) (y (1, true))
    (y (2, false)) (y (2, true)) (y (3, false)) (y (3, true)) r0 r0' r1 r1' r2 r2' r3 r3'
    (by linarith)
  have dec : ∀ a, y a = 0 → early a = true := by
    intro a ha; rcases hy a with ⟨_, h⟩ | ⟨h1, _⟩
    · exact h
    · omega
  have dec' : ∀ a, y a = 1 → early a = false := by
    intro a ha; rcases hy a with ⟨h1, _⟩ | ⟨_, h⟩
    · omega
    · exact h
  rcases key with ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ | ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩
  · refine ⟨true, ?_⟩
    rintro ⟨h, b⟩
    fin_cases h <;> cases b <;> simp only [sgn, eps] <;> norm_num
    · exact dec' _ a0
    · exact dec _ b0
    · exact dec _ a1
    · exact dec' _ b1
    · exact dec _ a2
    · exact dec' _ b2
    · exact dec _ a3
    · exact dec' _ b3
  · refine ⟨false, ?_⟩
    rintro ⟨h, b⟩
    fin_cases h <;> cases b <;> simp only [sgn, eps] <;> norm_num
    · exact dec _ a0
    · exact dec' _ b0
    · exact dec' _ a1
    · exact dec _ b1
    · exact dec' _ a2
    · exact dec _ b2
    · exact dec' _ a3
    · exact dec _ b3

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 5. Kernel field (Lemma I.12) and scale separation (Lemma I.14) -/

theorem lam_sub (u v : Fin X.n) : X.lam u - X.lam v = (v : ℤ) - u := by unfold lam; ring
theorem L_sub (u v : Fin X.n) : X.L u - X.L v = 2 * ((v : ℤ) - u) := by
  unfold L; rw [show 2 * X.lam u - 2 * X.lam v = 2 * (X.lam u - X.lam v) by ring, lam_sub]

theorem lam_ge (v : Fin X.n) : X.G + 1 ≤ X.lam v := by
  unfold lam; have : (v : ℤ) < X.n := by exact_mod_cast v.isLt
  linarith
theorem lam_le (v : Fin X.n) : X.lam v ≤ X.G + X.n := by
  unfold lam; have : (0:ℤ) ≤ (v : ℤ) := by positivity
  linarith

theorem abs_lam_sub_le (u v : Fin X.n) : |X.lam u - X.lam v| ≤ X.n := by
  rw [lam_sub, abs_le]
  have hu : (u : ℤ) < X.n := by exact_mod_cast u.isLt
  have hv : (v : ℤ) < X.n := by exact_mod_cast v.isLt
  have : (0:ℤ) ≤ u := by positivity
  have : (0:ℤ) ≤ v := by positivity
  constructor <;> linarith

theorem K_sub_bounds {u w : Fin X.n} (huw : u ≤ w) (v : Fin X.n) :
    0 ≤ X.K u v - X.K w v ∧ X.K u v - X.K w v ≤ X.L u - X.L w := by
  have hL : X.L w ≤ X.L u := by
    have := X.L_sub u w
    have : (u : ℤ) ≤ w := by exact_mod_cast huw
    linarith
  unfold K
  constructor
  · have := min_le_min_right (X.L v) hL; linarith
  · rcases le_total (X.L u) (X.L v) with h | h <;> rcases le_total (X.L w) (X.L v) with h' | h' <;>
      simp [h, h'] <;> linarith

theorem β_eq (v : Fin X.n) :
    X.β v = 4 * X.T + X.M * ((X.ht v 1 : ℤ) + X.ht v 2 + X.ht v 3) + 11113 := by
  unfold β; rw [Fin.sum_univ_four]; simp only [P, ht_zero, Qc]; push_cast; norm_num; ring

section
variable {X}
variable (hn : 0 < X.n)
include hn

/-- `3 n M + 11113 < T` -/
theorem scale_T : 3 * (X.n : ℤ) * X.M + 11113 < X.T := by
  have hnN := n_lt_NN hn
  have hMp : 0 < X.M := X.M_pos
  have e1 : 3 * (X.n : ℤ) * X.M ≤ 3 * (X.NN * X.NN ^ 40) := by
    have : (X.n : ℤ) * X.M ≤ X.NN * X.NN ^ 40 := mul_le_mul_of_nonneg_right hnN.le hMp.le
    linarith
  have e2 : 3 * (X.NN * X.NN ^ 40) ≤ X.NN ^ 49 := by
    have := mul_pow_le hn 3 41 8 (by norm_num)
    have e : X.NN * X.NN ^ 40 = X.NN ^ 41 := by ring
    rw [e]; simpa using this
  have e3 : (11113 : ℤ) < X.NN ^ 49 := by
    have := mul_pow_le hn 11114 0 7 (by norm_num)
    simp only [pow_zero, mul_one, zero_add] at this
    linarith [pow_mono hn (show 7 ≤ 49 by norm_num)]
  have e4 : 2 * X.NN ^ 49 ≤ X.NN ^ 50 := by
    have := mul_pow_le hn 2 49 1 (by norm_num); simpa using this
  rw [T_eq]; linarith

theorem β_bounds (v : Fin X.n) : 4 * X.T < X.β v ∧ X.β v < 5 * X.T := by
  rw [β_eq]
  have h1 : (X.ht v 1 : ℤ) ≤ X.n := by exact_mod_cast X.ht_le v 1
  have h2 : (X.ht v 2 : ℤ) ≤ X.n := by exact_mod_cast X.ht_le v 2
  have h3 : (X.ht v 3 : ℤ) ≤ X.n := by exact_mod_cast X.ht_le v 3
  have h0 : (0:ℤ) ≤ (X.ht v 1 : ℤ) + X.ht v 2 + X.ht v 3 := by positivity
  have hM := X.M_pos
  have := scale_T hn
  constructor
  · nlinarith
  · have : X.M * ((X.ht v 1 : ℤ) + X.ht v 2 + X.ht v 3) ≤ X.M * (3 * X.n) :=
      mul_le_mul_of_nonneg_left (by linarith) hM.le
    nlinarith

theorem sum_β_lt : ∑ v, X.β v < 5 * X.n * X.T := by
  have hne : (univ : Finset (Fin X.n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  have := Finset.sum_lt_sum_of_nonempty hne (fun v _ => (β_bounds hn v).2)
  simp at this; linarith

/-- **Lemma I.12** (consequences used later): the kernel field is decreasing in the block index,
strictly, and its total variation is `< 10 n² T`. -/
theorem f_sub_bounds {u w : Fin X.n} (huw : u ≤ w) :
    0 ≤ X.f u - X.f w ∧ X.f u - X.f w ≤ 10 * (X.n : ℤ) ^ 2 * X.T := by
  have hdiff : X.f u - X.f w = ∑ v, (X.K u v - X.K w v) * X.β v := by
    unfold f; rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => by ring)
  rw [hdiff]
  constructor
  · exact Finset.sum_nonneg (fun v _ =>
      mul_nonneg (X.K_sub_bounds huw v).1 (X.β_pos v).le)
  · have hLuw : X.L u - X.L w ≤ 2 * X.n := by
      rw [L_sub]
      have : (w : ℤ) < X.n := by exact_mod_cast w.isLt
      have : (0:ℤ) ≤ u := by positivity
      linarith
    have hLnn : 0 ≤ X.L u - X.L w := by
      have := (X.K_sub_bounds huw ⟨0, hn⟩); linarith
    calc ∑ v, (X.K u v - X.K w v) * X.β v ≤ ∑ v, (X.L u - X.L w) * X.β v :=
          Finset.sum_le_sum (fun v _ =>
            mul_le_mul_of_nonneg_right (X.K_sub_bounds huw v).2 (X.β_pos v).le)
      _ = (X.L u - X.L w) * ∑ v, X.β v := by rw [Finset.mul_sum]
      _ ≤ (2 * X.n) * (5 * X.n * X.T) := by
          have hs := sum_β_lt hn
          have hs0 : 0 ≤ ∑ v, X.β v := Finset.sum_nonneg (fun v _ => (X.β_pos v).le)
          have hT := X.T_pos
          have : (0:ℤ) ≤ 2 * X.n := by positivity
          calc (X.L u - X.L w) * ∑ v, X.β v ≤ (2 * X.n) * ∑ v, X.β v :=
                mul_le_mul_of_nonneg_right hLuw hs0
            _ ≤ (2 * X.n) * (5 * X.n * X.T) := mul_le_mul_of_nonneg_left hs.le this
      _ = 10 * (X.n : ℤ) ^ 2 * X.T := by ring

theorem f_strict {u w : Fin X.n} (huw : u < w) : X.f w < X.f u := by
  have hdiff : X.f u - X.f w = ∑ v, (X.K u v - X.K w v) * X.β v := by
    unfold f; rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => by ring)
  have hterm : 0 < (X.K u u - X.K w u) * X.β u := by
    apply mul_pos _ (X.β_pos u)
    unfold K
    have : X.L w < X.L u := by
      have := X.L_sub u w
      have : (u : ℤ) < w := by exact_mod_cast huw
      linarith
    rw [min_self, min_eq_left this.le]; linarith
  have := Finset.single_le_sum (f := fun v => (X.K u v - X.K w v) * X.β v)
    (fun v _ => mul_nonneg (X.K_sub_bounds huw.le v).1 (X.β_pos v).le) (mem_univ u)
  linarith

theorem abs_f_sub_le (u w : Fin X.n) : |X.f u - X.f w| ≤ 10 * (X.n : ℤ) ^ 2 * X.T := by
  rcases le_total u w with h | h
  · have := f_sub_bounds hn h; rw [abs_le]; constructor <;> linarith
  · have := f_sub_bounds hn h; rw [abs_le]; constructor <;> linarith

/-- the master numerical inequality behind all separations:
`10 n² T + 2 n T + 2 n² M + 20003 (G + n) < G M` -/
theorem scale_key :
    10 * (X.n : ℤ) ^ 2 * X.T + 2 * X.n * X.T + 2 * (X.n : ℤ) ^ 2 * X.M + 20003 * (X.G + X.n)
      < X.G * X.M := by
  have hnN := n_lt_NN hn
  have h4 := NN_ge_four hn
  have hn0 : (0:ℤ) ≤ X.n := by positivity
  have hN0 : (0:ℤ) ≤ X.NN := by linarith
  rw [G_eq, M_eq, T_eq]
  have hn2 : (X.n : ℤ) ^ 2 ≤ X.NN ^ 2 := pow_le_pow_left₀ hn0 hnN.le 2
  have p50 := pow_pos' hn 50
  have p40 := pow_pos' hn 40
  have t1 : 10 * (X.n : ℤ) ^ 2 * X.NN ^ 50 ≤ 10 * X.NN ^ 52 := by
    have := mul_le_mul_of_nonneg_right hn2 p50.le
    rw [show X.NN ^ 52 = X.NN ^ 2 * X.NN ^ 50 by ring]; linarith
  have t2 : 2 * (X.n : ℤ) * X.NN ^ 50 ≤ 2 * X.NN ^ 52 := by
    have := mul_le_mul_of_nonneg_right hnN.le p50.le
    have h51 : X.NN * X.NN ^ 50 ≤ X.NN ^ 52 := by
      rw [show X.NN * X.NN ^ 50 = X.NN ^ 51 by ring]; exact pow_mono hn (by norm_num)
    linarith
  have t3 : 2 * (X.n : ℤ) ^ 2 * X.NN ^ 40 ≤ 2 * X.NN ^ 52 := by
    have := mul_le_mul_of_nonneg_right hn2 p40.le
    have h42 : X.NN ^ 2 * X.NN ^ 40 ≤ X.NN ^ 52 := by
      rw [show X.NN ^ 2 * X.NN ^ 40 = X.NN ^ 42 by ring]; exact pow_mono hn (by norm_num)
    linarith
  have t4 : 20003 * (X.NN ^ 20 + X.n) ≤ 40006 * X.NN ^ 52 := by
    have a1 : X.NN ^ 20 ≤ X.NN ^ 52 := pow_mono hn (by norm_num)
    have a2 : (X.n : ℤ) ≤ X.NN ^ 52 := by
      have : X.NN ^ 1 ≤ X.NN ^ 52 := pow_mono hn (by norm_num)
      simp at this; linarith
    linarith
  have t5 : 65536 * X.NN ^ 52 ≤ X.NN ^ 60 := by
    have := mul_pow_le hn 65536 52 8 (by norm_num); simpa using this
  have p52 := pow_pos' hn 52
  rw [show X.NN ^ 20 * X.NN ^ 40 = X.NN ^ 60 by ring]
  linarith

end

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-- generic ratio value `f_u + λ_u (t (T + M a + Q) + c)`: `t = 1` gives physical early ratios,
`t = 2` gives effective ratios. -/
def valE (t : ℤ) (u : Fin X.n) (a Q c : ℤ) : ℤ := X.f u + X.lam u * (t * (X.T + X.M * a + Q) + c)

theorem rS_eq_valE (i : SJ X.n) :
    X.rS i = X.valE 1 i.1 (X.ht i.1 i.2.1) (Qc i.2.1) (if i.2.2 then 0 else cA i.2.1) := by
  unfold rS valE pS P; ring

theorem ρ_eq_valE (v : Fin X.n) (h : Fin 4) :
    X.ρ v h = X.valE 2 v (X.ht v h) (Qc h) (cA h) := by
  unfold ρ valE P; ring

theorem Qc_le (h : Fin 4) : Qc h ≤ 10000 := by
  unfold Qc; fin_cases h <;> norm_num
theorem Qc_nonneg (h : Fin 4) : 0 ≤ Qc h := (Qc_pos h).le
theorem cA_le (h : Fin 4) : cA h ≤ 3 := by unfold cA; split_ifs <;> norm_num

section
variable {X}
variable (hn : 0 < X.n)
include hn

theorem scale_T2 : 20003 * (X.G + X.n) < X.T := by
  have hnN := n_lt_NN hn
  rw [G_eq, T_eq]
  have a1 : X.NN ^ 20 ≤ X.NN ^ 30 := pow_mono hn (by norm_num)
  have a2 : (X.n : ℤ) ≤ X.NN ^ 30 := by
    have : X.NN ^ 1 ≤ X.NN ^ 30 := pow_mono hn (by norm_num)
    simp at this; linarith
  have a3 : 65536 * X.NN ^ 30 ≤ X.NN ^ 38 := by
    have := mul_pow_le hn 65536 30 8 (by norm_num); simpa using this
  have a4 : X.NN ^ 38 ≤ X.NN ^ 50 := pow_mono hn (by norm_num)
  have := pow_pos' hn 30
  linarith

/-- **Separation across heights** (Lemma I.14, different element levels). -/
theorem sep_lower (u v : Fin X.n) (a b Qa Qb ca cb t : ℤ) (ht : t = 1 ∨ t = 2)
    (hab : b + 1 ≤ a) (ha : a ≤ X.n) (hb : 0 ≤ b) (hQa : 0 ≤ Qa) (hQb : Qb ≤ 10000)
    (hca : 0 ≤ ca) (hcb : cb ≤ 3) (_hQb0 : 0 ≤ Qb) (_hcb0 : 0 ≤ cb) :
    (t - 1) * X.G * X.M < X.valE t u a Qa ca - X.valE t v b Qb cb := by
  unfold valE
  have hf := abs_f_sub_le hn u v
  have hl := X.abs_lam_sub_le u v
  have hlu := X.lam_ge u
  have hlv := X.lam_le v
  have hlv0 := X.lam_pos v
  have hT := X.T_pos
  have hM := X.M_pos
  have hG := X.G_pos
  have key := scale_key hn
  have hn0 : (0:ℤ) ≤ X.n := by positivity
  -- (λu - λv) T ≥ - n T
  have e1 : -(X.n * X.T) ≤ (X.lam u - X.lam v) * X.T := by
    have := abs_le.mp hl
    nlinarith
  -- λu a - λv b ≥ G + 1 - n²
  have e2 : X.G + 1 - (X.n : ℤ) ^ 2 ≤ X.lam u * a - X.lam v * b := by
    have h1 : X.lam u ≤ X.lam u * (a - b) := by nlinarith
    have h2 : -(X.n * b) ≤ (X.lam u - X.lam v) * b := by
      have := abs_le.mp hl; nlinarith
    have h3 : X.n * b ≤ (X.n : ℤ) ^ 2 := by nlinarith
    nlinarith
  have e3 : X.lam v * Qb ≤ (X.G + X.n) * 10000 := by nlinarith
  have e4 : X.lam v * cb ≤ (X.G + X.n) * 3 := by nlinarith
  have e5 : 0 ≤ X.lam u * Qa := by nlinarith
  have e6 : 0 ≤ X.lam u * ca := by nlinarith
  have hfuv := abs_le.mp hf
  rcases ht with rfl | rfl
  · have : X.M * (X.G + 1 - (X.n : ℤ) ^ 2) ≤ X.M * (X.lam u * a - X.lam v * b) :=
      mul_le_mul_of_nonneg_left e2 hM.le
    nlinarith
  · have : X.M * (X.G + 1 - (X.n : ℤ) ^ 2) ≤ X.M * (X.lam u * a - X.lam v * b) :=
      mul_le_mul_of_nonneg_left e2 hM.le
    nlinarith

/-- **Separation inside a height** (Lemma I.14, same element level): the smaller block index
lies higher. -/
theorem sep_same {u v : Fin X.n} (huv : u < v) (a Qa Qb ca cb t : ℤ) (ht : t = 1 ∨ t = 2)
    (ha : 0 ≤ a) (hQa : 0 ≤ Qa) (hQb : Qb ≤ 10000) (hca : 0 ≤ ca) (hcb : cb ≤ 3) :
    X.valE t v a Qb cb < X.valE t u a Qa ca := by
  unfold valE
  have hf := f_strict hn huv
  have hl : X.lam u - X.lam v = (v : ℤ) - u := X.lam_sub u v
  have hl1 : 1 ≤ X.lam u - X.lam v := by
    rw [hl]; have : (u : ℤ) < v := by exact_mod_cast huv
    linarith
  have hlv := X.lam_le v
  have hlu0 := X.lam_pos u
  have hlv0 := X.lam_pos v
  have hT := X.T_pos
  have hM := X.M_pos
  have k2 := scale_T2 hn
  have e7 : 0 ≤ X.M * a := mul_nonneg hM.le ha
  have e0 : X.T + X.M * a ≤ (X.lam u - X.lam v) * (X.T + X.M * a) := by
    have := mul_le_mul_of_nonneg_right hl1 (by linarith : (0:ℤ) ≤ X.T + X.M * a)
    linarith
  have e3 : X.lam v * Qb ≤ (X.G + X.n) * 10000 := by nlinarith
  have e4 : X.lam v * cb ≤ (X.G + X.n) * 3 := by nlinarith
  have e5 : 0 ≤ X.lam u * Qa := mul_nonneg hlu0.le hQa
  have e6 : 0 ≤ X.lam u * ca := mul_nonneg hlu0.le hca
  rcases ht with rfl | rfl <;> nlinarith

/-- width of a band: two effective atoms at the same height differ by at most `Wb` -/
def Wb (X : RXC3) : ℤ := 10 * (X.n : ℤ) ^ 2 * X.T + 2 * X.n * X.T + 2 * (X.n : ℤ) ^ 2 * X.M
  + 20003 * (X.G + X.n)

theorem width_same (u v : Fin X.n) (a Qa Qb ca cb : ℤ) (ha0 : 0 ≤ a) (ha : a ≤ X.n)
    (hQa : 0 ≤ Qa) (hQa' : Qa ≤ 10000) (hQb : 0 ≤ Qb) (hQb' : Qb ≤ 10000)
    (hca : 0 ≤ ca) (hca' : ca ≤ 3) (hcb : 0 ≤ cb) (hcb' : cb ≤ 3) :
    |X.valE 2 u a Qa ca - X.valE 2 v a Qb cb| ≤ X.Wb := by
  unfold valE Wb
  have hf := abs_le.mp (abs_f_sub_le hn u v)
  have hl := abs_le.mp (X.abs_lam_sub_le u v)
  have hlu := X.lam_le u
  have hlv := X.lam_le v
  have hlu0 := X.lam_pos u
  have hlv0 := X.lam_pos v
  have hT := X.T_pos
  have hM := X.M_pos
  have hn0 : (0:ℤ) ≤ X.n := by positivity
  have hTMa : 0 ≤ X.T + X.M * a := by nlinarith
  have hTMa' : X.T + X.M * a ≤ X.T + X.M * X.n := by nlinarith
  have e1 : |(X.lam u - X.lam v) * (X.T + X.M * a)| ≤ X.n * (X.T + X.M * X.n) := by
    rw [abs_mul, abs_of_nonneg hTMa]
    exact mul_le_mul (abs_le.mpr hl) hTMa' hTMa hn0
  have e1' := abs_le.mp e1
  have e3 : 0 ≤ X.lam u * (2 * Qa + ca) ∧ X.lam u * (2 * Qa + ca) ≤ (X.G + X.n) * 20003 := by
    constructor <;> nlinarith
  have e4 : 0 ≤ X.lam v * (2 * Qb + cb) ∧ X.lam v * (2 * Qb + cb) ≤ (X.G + X.n) * 20003 := by
    constructor <;> nlinarith
  rw [abs_le]
  constructor <;> nlinarith

end

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ### clusters, separation and exact pair compression (Lemma I.13) -/

/-- cluster `(u,g)` lies above cluster `(v,h)` in early-ratio space -/
def above (u : Fin X.n) (g : Fin 4) (v : Fin X.n) (h : Fin 4) : Prop :=
  X.ht v h < X.ht u g ∨ (X.ht u g = X.ht v h ∧ u < v)

theorem above_or_above {u v : Fin X.n} (huv : u ≠ v) (g h : Fin 4) :
    X.above u g v h ∨ X.above v h u g := by
  unfold above
  rcases lt_trichotomy (X.ht v h) (X.ht u g) with e | e | e
  · left; left; exact e
  · rcases lt_or_gt_of_ne huv with e' | e'
    · left; right; exact ⟨e.symm, e'⟩
    · right; right; exact ⟨e, e'⟩
  · right; left; exact e

theorem ht_int_le (v : Fin X.n) (h : Fin 4) : ((X.ht v h : ℕ) : ℤ) ≤ X.n := by
  exact_mod_cast X.ht_le v h

theorem slot_c_bounds (h : Fin 4) (b : Bool) :
    0 ≤ (if b then 0 else cA h) ∧ (if b then 0 else cA h) ≤ 3 := by
  have := cA_pos h; have := cA_le h
  split_ifs <;> constructor <;> linarith

section
variable {X}
variable (hn : 0 < X.n)
include hn

/-- physical separation of clusters (first half of Lemma I.14) -/
theorem phys_sep {u v : Fin X.n} {g h : Fin 4} (hab : X.above u g v h) (b b' : Bool) :
    X.rS (v, h, b') < X.rS (u, g, b) := by
  rw [rS_eq_valE, rS_eq_valE]
  simp only
  have hc := slot_c_bounds g b
  have hc' := slot_c_bounds h b'
  rcases hab with hlt | ⟨heq, huv⟩
  · have := sep_lower hn u v (X.ht u g) (X.ht v h) (Qc g) (Qc h) _ _ 1 (Or.inl rfl)
      (by exact_mod_cast hlt) (X.ht_int_le u g) (by positivity) (Qc_nonneg g) (Qc_le h)
      hc.1 hc'.2 (Qc_nonneg h) hc'.1
    simp at this; linarith
  · rw [heq]
    exact sep_same hn huv _ _ _ _ _ 1 (Or.inl rfl) (by positivity) (Qc_nonneg g) (Qc_le h)
      hc.1 hc'.2

/-- effective separation of clusters -/
theorem eff_sep {u v : Fin X.n} {g h : Fin 4} (hab : X.above u g v h) : X.ρ v h < X.ρ u g := by
  rw [ρ_eq_valE, ρ_eq_valE]
  rcases hab with hlt | ⟨heq, huv⟩
  · have := sep_lower hn u v (X.ht u g) (X.ht v h) (Qc g) (Qc h) _ _ 2 (Or.inr rfl)
      (by exact_mod_cast hlt) (X.ht_int_le u g) (by positivity) (Qc_nonneg g) (Qc_le h)
      (cA_pos g).le (cA_le h) (Qc_nonneg h) (cA_pos h).le
    have hGM : 0 < X.G * X.M := mul_pos X.G_pos X.M_pos
    nlinarith
  · rw [heq]
    exact sep_same hn huv _ _ _ _ _ 2 (Or.inr rfl) (by positivity) (Qc_nonneg g) (Qc_le h)
      (cA_pos g).le (cA_le h)

/-- the main gap: consecutive heights are separated by more than `G M` -/
theorem eff_gap {u v : Fin X.n} {g h : Fin 4} (hht : X.ht v h + 1 = X.ht u g) :
    X.ρ v h + X.G * X.M < X.ρ u g := by
  rw [ρ_eq_valE, ρ_eq_valE]
  have := sep_lower hn u v (X.ht u g) (X.ht v h) (Qc g) (Qc h) _ _ 2 (Or.inr rfl)
    (by rw [← hht]; push_cast; linarith) (X.ht_int_le u g) (by positivity) (Qc_nonneg g) (Qc_le h)
    (cA_pos g).le (cA_le h) (Qc_nonneg h) (cA_pos h).le
  linarith

/-- band width bound -/
theorem eff_width {u v : Fin X.n} {g h : Fin 4} (hht : X.ht u g = X.ht v h) :
    |X.ρ u g - X.ρ v h| ≤ X.Wb := by
  rw [ρ_eq_valE, ρ_eq_valE, hht]
  exact width_same hn u v _ _ _ _ _ (by positivity) (X.ht_int_le v h) (Qc_nonneg g) (Qc_le g)
    (Qc_nonneg h) (Qc_le h) (cA_pos g).le (cA_le g) (cA_pos h).le (cA_le h)

end

/-- `Σ_b ε p = m_h` -/
theorem pair_mass (v : Fin X.n) (h : Fin 4) :
    ∑ b : Bool, eps h b * X.pS (v, h, b) = mass h := by
  rw [Fintype.sum_bool, add_comm]; exact X.sum_eps_pS_pair v h

/-- first moment of a cluster: `Σ_b ε p r = m_h ρ_h` -/
theorem pair_moment (v : Fin X.n) (h : Fin 4) :
    ∑ b : Bool, eps h b * X.wES (v, h, b) = mass h * X.ρ v h := by
  rw [Fintype.sum_bool]
  have h1 := X.sum_eps_pS_pair v h
  have h2 := X.sum_eps_pS2_pair v h
  simp only [wES, rS, ρ] at *
  linear_combination (X.f v) * h1 + (X.lam v) * h2

theorem α_of_rS_lt {i j : SJ X.n} (h : X.rS j < X.rS i) : X.α i j = X.pS i * X.wES j := by
  unfold α wES
  have hpi := X.pS_pos i; have hpj := X.pS_pos j
  have : X.pS i * (X.pS j * X.rS j) ≤ X.pS j * (X.pS i * X.rS i) := by
    have := mul_le_mul_of_nonneg_left h.le (mul_pos hpi hpj).le
    nlinarith
  exact min_eq_right this

theorem α_symm (i j : SJ X.n) : X.α i j = X.α j i := by unfold α; rw [min_comm]

/-- **Lemma I.13 (exact pair compression).** For clusters of different blocks the four signed
physical early interactions equal `m_g m_h min(ρ_g, ρ_h)`. -/
theorem pair_compress (hn : 0 < X.n) {u v : Fin X.n} (huv : u ≠ v) (g h : Fin 4) :
    ∑ b : Bool, ∑ b' : Bool, eps g b * eps h b' * X.α (u, g, b) (v, h, b')
      = mass g * mass h * min (X.ρ u g) (X.ρ v h) := by
  rcases X.above_or_above huv g h with hab | hab
  · have hr : ∀ b b', X.α (u, g, b) (v, h, b') = X.pS (u, g, b) * X.wES (v, h, b') :=
      fun b b' => X.α_of_rS_lt (phys_sep hn hab b b')
    simp only [hr]
    rw [min_eq_right (eff_sep hn hab).le,
      show mass g * mass h * X.ρ v h = mass g * (mass h * X.ρ v h) by ring,
      ← X.pair_mass u g, ← X.pair_moment v h, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    ring
  · have hr : ∀ b b', X.α (u, g, b) (v, h, b') = X.pS (v, h, b') * X.wES (u, g, b) := by
      intro b b'; rw [X.α_symm]; exact X.α_of_rS_lt (phys_sep hn hab b' b)
    simp only [hr]
    rw [min_eq_left (eff_sep hn hab).le,
      show mass g * mass h * X.ρ u g = (mass g * X.ρ u g) * mass h by ring,
      ← X.pair_mass v h, ← X.pair_moment u g]
    rw [show (∑ b : Bool, eps g b * X.wES (u, g, b)) * (∑ b' : Bool, eps h b' * X.pS (v, h, b'))
        = ∑ b : Bool, ∑ b' : Bool, (eps g b * X.wES (u, g, b)) * (eps h b' * X.pS (v, h, b'))
        by rw [Finset.sum_mul_sum]]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => ?_))
    ring

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 6. Effective bands, main gaps and the profile decomposition of `J_{uv}` -/

theorem mem_atomsAt (v : Fin X.n) (h : Fin 4) : (v, h) ∈ X.atomsAt (X.ht v h) :=
  Finset.mem_filter.mpr ⟨mem_univ _, rfl⟩

theorem atomsAt_ne (v : Fin X.n) (h : Fin 4) : (X.atomsAt (X.ht v h)).Nonempty :=
  ⟨(v, h), X.mem_atomsAt v h⟩

theorem lo_le_ρ (v : Fin X.n) (h : Fin 4) : X.lo (X.ht v h) ≤ X.ρ v h := by
  unfold lo; rw [dite_eq_left (X.atomsAt_ne v h)]
  exact Finset.inf'_le (s := X.atomsAt (X.ht v h)) (fun a => X.ρ a.1 a.2) (X.mem_atomsAt v h)

theorem ρ_le_hi (v : Fin X.n) (h : Fin 4) : X.ρ v h ≤ X.hi (X.ht v h) := by
  unfold hi; rw [dite_eq_left (X.atomsAt_ne v h)]
  exact Finset.le_sup' (s := X.atomsAt (X.ht v h)) (fun a => X.ρ a.1 a.2) (X.mem_atomsAt v h)

theorem lo_attained (η : ℕ) (hne : (X.atomsAt η).Nonempty) :
    ∃ a ∈ X.atomsAt η, X.lo η = X.ρ a.1 a.2 := by
  unfold lo; rw [dite_eq_left hne]
  exact Finset.exists_mem_eq_inf' (s := X.atomsAt η) hne (fun a => X.ρ a.1 a.2)

theorem hi_attained (η : ℕ) (hne : (X.atomsAt η).Nonempty) :
    ∃ a ∈ X.atomsAt η, X.hi η = X.ρ a.1 a.2 := by
  unfold hi; rw [dite_eq_left hne]
  exact Finset.exists_mem_eq_sup' (s := X.atomsAt η) hne (fun a => X.ρ a.1 a.2)

theorem ht_of_mem {η : ℕ} {a : Fin X.n × Fin 4} (ha : a ∈ X.atomsAt η) : X.ht a.1 a.2 = η :=
  (Finset.mem_filter.mp ha).2

/-- every height `0,…,n` carries at least one effective atom -/
theorem atomsAt_nonempty (hn : 0 < X.n) {η : ℕ} (hη : η ≤ X.n) : (X.atomsAt η).Nonempty := by
  rcases Nat.eq_zero_or_pos η with rfl | hpos
  · exact ⟨(⟨0, hn⟩, 0), by simp [atomsAt, ht_zero]⟩
  · -- element `k = n - η` occurs in some set
    have hk : X.n - η < X.n := by omega
    have hc := X.reg ⟨X.n - η, hk⟩
    have : (univ.filter (fun q : Fin X.n × Fin 3 => X.S q.1 q.2 = ⟨X.n - η, hk⟩)).Nonempty := by
      rw [← Finset.card_pos, hc]; norm_num
    obtain ⟨⟨v, h'⟩, hq⟩ := this
    have hq' : X.S v h' = ⟨X.n - η, hk⟩ := by simpa using hq
    refine ⟨(v, ⟨h'.val + 1, by omega⟩), ?_⟩
    simp only [atomsAt, mem_filter, mem_univ, true_and]
    unfold ht
    rw [dite_eq_right (by simp)]
    have : (⟨h'.val + 1 - 1, by omega⟩ : Fin 3) = h' := by ext; simp
    simp only [Nat.add_sub_cancel] at this ⊢
    rw [show (⟨h'.val, by omega⟩ : Fin 3) = h' from rfl, hq']
    simp; omega

section
variable {X}
variable (hn : 0 < X.n)
include hn

theorem lo_le_hi {η : ℕ} (hη : η ≤ X.n) : X.lo η ≤ X.hi η := by
  obtain ⟨a, ha, hlo⟩ := X.lo_attained η (X.atomsAt_nonempty hn hη)
  have := X.ρ_le_hi a.1 a.2
  rw [X.ht_of_mem ha] at this
  linarith

/-- main gaps exceed `G M` -/
theorem gap_gt {η : ℕ} (hη : η < X.n) : X.G * X.M < X.gap η := by
  unfold gap
  obtain ⟨a, ha, hhi⟩ := X.hi_attained η (X.atomsAt_nonempty hn hη.le)
  obtain ⟨b, hb, hlo⟩ := X.lo_attained (η + 1) (X.atomsAt_nonempty hn hη)
  have := eff_gap hn (u := b.1) (v := a.1) (g := b.2) (h := a.2)
    (by rw [X.ht_of_mem ha, X.ht_of_mem hb])
  rw [hhi, hlo]; linarith

theorem width_le {η : ℕ} (hη : η ≤ X.n) : X.hi η - X.lo η ≤ X.Wb := by
  obtain ⟨a, ha, hhi⟩ := X.hi_attained η (X.atomsAt_nonempty hn hη)
  obtain ⟨b, hb, hlo⟩ := X.lo_attained η (X.atomsAt_nonempty hn hη)
  have := eff_width hn (u := a.1) (v := b.1) (g := a.2) (h := b.2)
    (by rw [X.ht_of_mem ha, X.ht_of_mem hb])
  rw [hhi, hlo]; exact le_trans (le_abs_self _) this

theorem hi_lt_lo {η η' : ℕ} (h : η < η') (hη' : η' ≤ X.n) : X.hi η < X.lo η' := by
  induction η' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · have := ih h1 (by omega)
      have := lo_le_hi hn (show k ≤ X.n by omega)
      have := gap_gt hn (show k < X.n by omega)
      have := mul_pos X.G_pos X.M_pos
      unfold gap at *; linarith
    · subst h1
      have := gap_gt hn (show η < X.n by omega)
      have := mul_pos X.G_pos X.M_pos
      unfold gap at *; linarith

/-- an atom above height `η` lies above the whole band `η` -/
theorem hi_lt_ρ {η : ℕ} {v : Fin X.n} {h : Fin 4} (hlt : η < X.ht v h) : X.hi η < X.ρ v h :=
  lt_of_lt_of_le (hi_lt_lo hn hlt (X.ht_le v h)) (X.lo_le_ρ v h)

/-- an atom below height `η` lies below the whole band `η` -/
theorem ρ_lt_lo {η : ℕ} (hη : η ≤ X.n) {v : Fin X.n} {h : Fin 4} (hlt : X.ht v h < η) :
    X.ρ v h < X.lo η :=
  lt_of_le_of_lt (X.ρ_le_hi v h) (hi_lt_lo hn hlt hη)

end

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ### layer decomposition of `min` -/

def clampZ (x a b : ℤ) : ℤ := max a (min x b)

theorem clampZ_split {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (x : ℤ) :
    clampZ x a c - a = (clampZ x a b - a) + (clampZ x b c - b) := by
  unfold clampZ
  rcases le_total x a with h1 | h1 <;> rcases le_total x b with h2 | h2 <;>
    rcases le_total x c with h3 | h3 <;>
    simp [*] <;> first | linarith | omega

theorem clampZ_mono (a b : ℤ) : Monotone (fun x => clampZ x a b) := by
  intro x y hxy
  unfold clampZ
  exact max_le_max (le_refl a) (min_le_min_right b hxy)

theorem clampZ_min (a b x y : ℤ) : clampZ (min x y) a b = min (clampZ x a b) (clampZ y a b) :=
  (clampZ_mono a b).map_min

theorem clampZ_of_le {x a b : ℤ} (_hab : a ≤ b) (h : x ≤ a) : clampZ x a b = a := by
  unfold clampZ; rw [max_eq_left]; exact le_trans (min_le_left _ _) h
theorem clampZ_of_ge {x a b : ℤ} (hab : a ≤ b) (h : b ≤ x) : clampZ x a b = b := by
  unfold clampZ; rw [min_eq_right h, max_eq_right hab]
theorem clampZ_of_mem {x a b : ℤ} (h1 : a ≤ x) (h2 : x ≤ b) : clampZ x a b = x := by
  unfold clampZ; rw [min_eq_left h2, max_eq_right h1]

/-- band part and gap part of a point -/
def bp (η : ℕ) (x : ℤ) : ℤ := clampZ x (X.lo η) (X.hi η) - X.lo η
def gp (η : ℕ) (x : ℤ) : ℤ := clampZ x (X.hi η) (X.lo (η + 1)) - X.hi η

section
variable {X}
variable (hn : 0 < X.n)
include hn

theorem lo0_le_hi {m : ℕ} (hm : m ≤ X.n) : X.lo 0 ≤ X.hi m := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exact lo_le_hi hn (Nat.zero_le _)
  · have := hi_lt_lo hn hpos hm
    have := lo_le_hi hn (Nat.zero_le X.n)
    have := lo_le_hi hn hm
    have := lo_le_hi hn (show 0 ≤ X.n by omega)
    have h0 := lo_le_hi hn (show (0:ℕ) ≤ X.n by omega)
    linarith

theorem layer_telescope (x : ℤ) : ∀ m, m ≤ X.n →
    clampZ x (X.lo 0) (X.hi m) - X.lo 0
      = ∑ η ∈ range (m + 1), X.bp η x + ∑ η ∈ range m, X.gp η x := by
  intro m
  induction m with
  | zero => intro _; simp [bp]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have c1 : X.lo 0 ≤ X.hi k := lo0_le_hi hn (by omega)
    have c2 : X.hi k ≤ X.lo (k + 1) := (hi_lt_lo hn (Nat.lt_succ_self k) hk).le
    have c3 : X.lo (k + 1) ≤ X.hi (k + 1) := lo_le_hi hn hk
    rw [clampZ_split c1 (le_trans c2 c3), h1, clampZ_split c2 c3]
    rw [Finset.sum_range_succ (fun η => X.bp η x) (k + 1), Finset.sum_range_succ (fun η => X.gp η x) k]
    unfold bp gp
    ring

theorem layer_decomp {x : ℤ} (h1 : X.lo 0 ≤ x) (h2 : x ≤ X.hi X.n) :
    x = X.lo 0 + ∑ η ∈ range (X.n + 1), X.bp η x + ∑ η ∈ range X.n, X.gp η x := by
  have := layer_telescope hn x X.n le_rfl
  rw [clampZ_of_mem h1 h2] at this
  linarith

theorem atom_in_range (v : Fin X.n) (h : Fin 4) : X.lo 0 ≤ X.ρ v h ∧ X.ρ v h ≤ X.hi X.n := by
  constructor
  · rcases Nat.eq_zero_or_pos (X.ht v h) with e | e
    · have := X.lo_le_ρ v h; rw [e] at this; exact this
    · have := hi_lt_lo hn e (X.ht_le v h)
      have := X.lo_le_ρ v h
      have := lo_le_hi hn (Nat.zero_le X.n)
      have h00 := lo_le_hi hn (show (0:ℕ) ≤ X.n by omega)
      linarith
  · rcases Nat.lt_or_ge (X.ht v h) X.n with e | e
    · have := hi_lt_lo hn e le_rfl
      have := X.ρ_le_hi v h
      have := lo_le_hi hn (le_refl X.n)
      linarith
    · have he : X.ht v h = X.n := le_antisymm (X.ht_le v h) e
      have := X.ρ_le_hi v h; rw [he] at this; exact this

/-- gap part of an effective atom -/
theorem gp_atom {η : ℕ} (hη : η < X.n) (v : Fin X.n) (h : Fin 4) :
    X.gp η (X.ρ v h) = if η < X.ht v h then X.gap η else 0 := by
  have c2 : X.hi η ≤ X.lo (η + 1) := (hi_lt_lo hn (Nat.lt_succ_self η) hη).le
  unfold gp gap
  split_ifs with hlt
  · rw [clampZ_of_ge c2]
    -- ρ ≥ lo (η+1)
    rcases Nat.lt_or_ge (η + 1) (X.ht v h) with e | e
    · have := hi_lt_lo hn e (X.ht_le v h)
      have := X.lo_le_ρ v h
      have := lo_le_hi hn (show η + 1 ≤ X.n by omega)
      linarith
    · have he : X.ht v h = η + 1 := by omega
      have := X.lo_le_ρ v h; rw [he] at this; exact this
  · rw [clampZ_of_le c2]
    · ring
    · rcases Nat.lt_or_ge (X.ht v h) η with e | e
      · have := hi_lt_lo hn e (show η ≤ X.n by omega)
        have := X.ρ_le_hi v h
        have := lo_le_hi hn (show η ≤ X.n by omega)
        linarith
      · have he : X.ht v h = η := by omega
        have := X.ρ_le_hi v h; rw [he] at this; exact this

/-- band part of an effective atom -/
theorem bp_atom {η : ℕ} (hη : η ≤ X.n) (v : Fin X.n) (h : Fin 4) :
    X.bp η (X.ρ v h) = if η < X.ht v h then X.hi η - X.lo η
      else if X.ht v h = η then X.ρ v h - X.lo η else 0 := by
  have c := lo_le_hi hn hη
  unfold bp
  split_ifs with h1 h2
  · rw [clampZ_of_ge c (hi_lt_ρ hn h1).le]
  · rw [clampZ_of_mem]
    · have := X.lo_le_ρ v h; rw [h2] at this; exact this
    · have := X.ρ_le_hi v h; rw [h2] at this; exact this
  · rw [clampZ_of_le c (ρ_lt_lo hn hη (by omega)).le]; ring

end

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-- `4 J_{uv}`: the signed early interaction of two blocks (8.10), first line -/
def J4 (u v : Fin X.n) : ℤ :=
  ∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool, eps a.1 a.2 * eps b.1 b.2 * X.α (u, a) (v, b)

theorem J4_compress (hn : 0 < X.n) {u v : Fin X.n} (huv : u ≠ v) :
    X.J4 u v = ∑ g : Fin 4, ∑ h : Fin 4, mass g * mass h * min (X.ρ u g) (X.ρ v h) := by
  unfold J4
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  exact X.pair_compress hn huv g h

/-- `Σ_g [P g] m_g φ(x_g)` when at most one `g` satisfies `P` -/
theorem sum_atMostOne {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (hP : ∀ g g', P g → P g' → g = g') (m x : ι → ℤ) (φ : ℤ → ℤ) :
    (∑ g, if P g then m g * φ (x g) else 0)
      = (∑ g, if P g then m g else 0) * φ (∑ g, if P g then x g else 0) := by
  by_cases hex : ∃ g, P g
  · obtain ⟨g0, hg0⟩ := hex
    have e : ∀ (F : ι → ℤ), (∑ g, if P g then F g else 0) = F g0 := by
      intro F
      rw [Finset.sum_eq_single g0]
      · simp [hg0]
      · intro b _ hb; rw [ite_eq_right]; intro hPb; exact hb (hP b g0 hPb hg0)
      · intro h; exact absurd (mem_univ g0) h
    rw [e, e, e]
  · push Not at hex
    simp [hex]

/-- mass of block `u` strictly above height `η` -/
def Mab (u : Fin X.n) (η : ℕ) : ℤ := ∑ g : Fin 4, if η < X.ht u g then mass g else 0
/-- mass of block `u` at height `η` -/
def Mat (u : Fin X.n) (η : ℕ) : ℤ := ∑ g : Fin 4, if X.ht u g = η then mass g else 0
/-- offset of the atom of block `u` at height `η` inside its band (0 if none) -/
def Oat (u : Fin X.n) (η : ℕ) : ℤ := ∑ g : Fin 4, if X.ht u g = η then X.ρ u g - X.lo η else 0

/-- the band-`η` contribution to `4 J_{uv}` -/
def bandSum (η : ℕ) (u v : Fin X.n) : ℤ :=
  ∑ g : Fin 4, ∑ h : Fin 4, mass g * mass h * min (X.bp η (X.ρ u g)) (X.bp η (X.ρ v h))

section
variable {X}
variable (hn : 0 < X.n)
include hn

theorem Oat_bounds {η : ℕ} (hη : η ≤ X.n) (u : Fin X.n) :
    0 ≤ X.Oat u η ∧ X.Oat u η ≤ X.hi η - X.lo η := by
  have hP : ∀ g g', X.ht u g = η → X.ht u g' = η → g = g' := fun g g' h1 h2 =>
    X.ht_inj u (h1.trans h2.symm)
  by_cases hex : ∃ g, X.ht u g = η
  · obtain ⟨g0, hg0⟩ := hex
    have e : X.Oat u η = X.ρ u g0 - X.lo η := by
      unfold Oat
      rw [Finset.sum_eq_single g0]
      · simp [hg0]
      · intro b _ hb; rw [ite_eq_right]; intro hPb; exact hb (hP b g0 hPb hg0)
      · intro h; exact absurd (mem_univ g0) h
    rw [e]
    have h1 := X.lo_le_ρ u g0; have h2 := X.ρ_le_hi u g0
    rw [hg0] at h1 h2
    constructor <;> linarith
  · push Not at hex
    have : X.Oat u η = 0 := by unfold Oat; simp [hex]
    rw [this]; have := lo_le_hi hn hη; constructor <;> linarith

theorem row_eq {η : ℕ} (hη : η ≤ X.n) (u : Fin X.n) {y : ℤ} (hy0 : 0 ≤ y)
    (hyw : y ≤ X.hi η - X.lo η) :
    ∑ g : Fin 4, mass g * min (X.bp η (X.ρ u g)) y = X.Mab u η * y + X.Mat u η * min (X.Oat u η) y := by
  have hP : ∀ g g', X.ht u g = η → X.ht u g' = η → g = g' := fun g g' h1 h2 =>
    X.ht_inj u (h1.trans h2.symm)
  have hsplit : ∀ g : Fin 4, mass g * min (X.bp η (X.ρ u g)) y
      = (if η < X.ht u g then mass g else 0) * y
        + (if X.ht u g = η then mass g * min (X.ρ u g - X.lo η) y else 0) := by
    intro g
    rw [bp_atom hn hη]
    by_cases h1 : η < X.ht u g
    · have h2 : X.ht u g ≠ η := by omega
      simp [h1, h2, min_eq_right hyw]
    · by_cases h2 : X.ht u g = η
      · simp [h2]
      · simp [h1, h2, min_eq_left hy0]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [sum_atMostOne (fun g => X.ht u g = η) hP mass (fun g => X.ρ u g - X.lo η) (fun t => min t y)]
  rfl

theorem bp_atom_bounds {η : ℕ} (hη : η ≤ X.n) (v : Fin X.n) (h : Fin 4) :
    0 ≤ X.bp η (X.ρ v h) ∧ X.bp η (X.ρ v h) ≤ X.hi η - X.lo η := by
  rw [bp_atom hn hη]
  have c := lo_le_hi hn hη
  split_ifs with h1 h2
  · constructor <;> linarith
  · have a1 := X.lo_le_ρ v h; have a2 := X.ρ_le_hi v h
    rw [h2] at a1 a2
    constructor <;> linarith
  · constructor <;> linarith

theorem bandSum_eq {η : ℕ} (hη : η ≤ X.n) (u v : Fin X.n) :
    X.bandSum η u v = X.Mab u η * (X.Mab v η * (X.hi η - X.lo η) + X.Mat v η * X.Oat v η)
      + X.Mat u η * (X.Mab v η * X.Oat u η + X.Mat v η * min (X.Oat v η) (X.Oat u η)) := by
  have hw := lo_le_hi hn hη
  have hOu := Oat_bounds hn hη u
  have hOv := Oat_bounds hn hη v
  unfold bandSum
  rw [Finset.sum_comm]
  have step : ∀ h : Fin 4, ∑ g : Fin 4, mass g * mass h * min (X.bp η (X.ρ u g)) (X.bp η (X.ρ v h))
      = mass h * (X.Mab u η * X.bp η (X.ρ v h)
          + X.Mat u η * min (X.Oat u η) (X.bp η (X.ρ v h))) := by
    intro h
    have hb := bp_atom_bounds hn hη v h
    rw [← row_eq hn hη u hb.1 hb.2, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => by ring)
  simp only [step]
  -- now sum over h
  have r1 := row_eq hn hη v (le_refl 0 |>.trans (le_refl 0) |> fun _ => (sub_nonneg.mpr hw))
    (le_refl (X.hi η - X.lo η))
  have r2 := row_eq hn hη v hOu.1 hOu.2
  have e1 : ∑ h : Fin 4, mass h * X.bp η (X.ρ v h)
      = ∑ h : Fin 4, mass h * min (X.bp η (X.ρ v h)) (X.hi η - X.lo η) := by
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [min_eq_left (bp_atom_bounds hn hη v h).2]
  have e2 : ∑ h : Fin 4, mass h * min (X.Oat u η) (X.bp η (X.ρ v h))
      = ∑ h : Fin 4, mass h * min (X.bp η (X.ρ v h)) (X.Oat u η) := by
    refine Finset.sum_congr rfl (fun h _ => by rw [min_comm])
  have hsum : ∑ h : Fin 4, mass h * (X.Mab u η * X.bp η (X.ρ v h)
          + X.Mat u η * min (X.Oat u η) (X.bp η (X.ρ v h)))
      = X.Mab u η * (∑ h : Fin 4, mass h * X.bp η (X.ρ v h))
        + X.Mat u η * (∑ h : Fin 4, mass h * min (X.Oat u η) (X.bp η (X.ρ v h))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun h _ => by ring)
  rw [hsum, e1, e2, r1, r2, min_eq_left hOv.2]

theorem Mab_zero (u : Fin X.n) : X.Mab u 0 = 3 := by
  unfold Mab
  rw [Fin.sum_univ_four]
  have p1 := X.ht_pos u 1 (by decide)
  have p2 := X.ht_pos u 2 (by decide)
  have p3 := X.ht_pos u 3 (by decide)
  simp [ht_zero, mass, show 0 < X.ht u 1 by omega, show 0 < X.ht u 2 by omega,
    show 0 < X.ht u 3 by omega]

theorem Mat_zero (u : Fin X.n) : X.Mat u 0 = -3 := by
  unfold Mat
  rw [Fin.sum_univ_four]
  have p1 := X.ht_pos u 1 (by decide)
  have p2 := X.ht_pos u 2 (by decide)
  have p3 := X.ht_pos u 3 (by decide)
  simp [ht_zero, mass, show X.ht u 1 ≠ 0 by omega, show X.ht u 2 ≠ 0 by omega,
    show X.ht u 3 ≠ 0 by omega]

theorem Mab_Mat_pos {η : ℕ} (hη : 1 ≤ η) (u : Fin X.n) :
    0 ≤ X.Mab u η ∧ 0 ≤ X.Mat u η ∧ X.Mab u η + X.Mat u η ≤ 3 := by
  unfold Mab Mat
  simp only [Fin.sum_univ_four, ht_zero, mass]
  have n1 : ¬ η < 0 := by omega
  have n2 : (0:ℕ) ≠ η := by omega
  simp only [n1, n2, ite_false]
  norm_num
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> norm_num <;> omega

/-- each band contributes between `0` and `9 × width` -/
theorem bandSum_bounds {η : ℕ} (hη : η ≤ X.n) (u v : Fin X.n) :
    0 ≤ X.bandSum η u v ∧ X.bandSum η u v ≤ 9 * (X.hi η - X.lo η) := by
  rw [bandSum_eq hn hη]
  have hw := lo_le_hi hn hη
  have hOu := Oat_bounds hn hη u
  have hOv := Oat_bounds hn hη v
  set w := X.hi η - X.lo η
  rcases Nat.eq_zero_or_pos η with rfl | hpos
  · rw [Mab_zero hn, Mab_zero hn, Mat_zero hn, Mat_zero hn]
    have hm1 := min_le_left (X.Oat v 0) (X.Oat u 0)
    have hm2 := min_le_right (X.Oat v 0) (X.Oat u 0)
    have hm3 : X.Oat v 0 ≤ min (X.Oat v 0) (X.Oat u 0) ∨ X.Oat u 0 ≤ min (X.Oat v 0) (X.Oat u 0) := by
      rcases le_total (X.Oat v 0) (X.Oat u 0) with h | h
      · left; rw [min_eq_left h]
      · right; rw [min_eq_right h]
    constructor
    · rcases hm3 with h | h <;> nlinarith
    · nlinarith
  · obtain ⟨a1, a2, a3⟩ := Mab_Mat_pos hn hpos u
    obtain ⟨b1, b2, b3⟩ := Mab_Mat_pos hn hpos v
    have hmin0 : 0 ≤ min (X.Oat v η) (X.Oat u η) := le_min hOv.1 hOu.1
    have hminw : min (X.Oat v η) (X.Oat u η) ≤ w := le_trans (min_le_left _ _) hOv.2
    constructor
    · have t1 : 0 ≤ X.Mab u η * (X.Mab v η * w + X.Mat v η * X.Oat v η) := by
        apply mul_nonneg a1; nlinarith
      have t2 : 0 ≤ X.Mat u η * (X.Mab v η * X.Oat u η + X.Mat v η * min (X.Oat v η) (X.Oat u η)) := by
        apply mul_nonneg a2; nlinarith
      linarith
    · have t1 : X.Mab v η * w + X.Mat v η * X.Oat v η ≤ (X.Mab v η + X.Mat v η) * w := by nlinarith
      have t2 : X.Mab v η * X.Oat u η + X.Mat v η * min (X.Oat v η) (X.Oat u η)
          ≤ (X.Mab v η + X.Mat v η) * w := by nlinarith
      have t3 : (X.Mab v η + X.Mat v η) * w ≤ 3 * w := by nlinarith
      have t4 : X.Mab u η * (X.Mab v η * w + X.Mat v η * X.Oat v η) ≤ X.Mab u η * (3 * w) :=
        mul_le_mul_of_nonneg_left (le_trans t1 t3) a1
      have t5 : X.Mat u η * (X.Mab v η * X.Oat u η + X.Mat v η * min (X.Oat v η) (X.Oat u η))
          ≤ X.Mat u η * (3 * w) := mul_le_mul_of_nonneg_left (le_trans t2 t3) a2
      nlinarith

end

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

theorem Mab_eq_dpre {η : ℕ} (hη : η < X.n) (u : Fin X.n) : X.Mab u η = X.dpre u (X.n - η) := by
  unfold Mab dpre
  rw [Fin.sum_univ_four, Finset.card_filter, Fin.sum_univ_three]
  have s0 := (X.S u 0).isLt; have s1 := (X.S u 1).isLt; have s2 := (X.S u 2).isLt
  have e0 : (η < X.ht u 1) ↔ ((X.S u 0 : ℕ) < X.n - η) := by rw [ht_one]; omega
  have e1 : (η < X.ht u 2) ↔ ((X.S u 1 : ℕ) < X.n - η) := by rw [ht_two]; omega
  have e2 : (η < X.ht u 3) ↔ ((X.S u 2 : ℕ) < X.n - η) := by rw [ht_three]; omega
  have m1 : mass 1 = 1 := by simp [mass]
  have m2 : mass 2 = 1 := by simp [mass]
  have m3 : mass 3 = 1 := by simp [mass]
  have z : ¬ η < X.ht u 0 := by rw [ht_zero]; omega
  simp only [z, ite_false, e0, e1, e2, m1, m2, m3, zero_add]
  push_cast
  split_ifs <;> norm_num

theorem bp_min (η : ℕ) (x y : ℤ) : X.bp η (min x y) = min (X.bp η x) (X.bp η y) := by
  unfold bp; rw [clampZ_min, min_sub_sub_right]
theorem gp_min (η : ℕ) (x y : ℤ) : X.gp η (min x y) = min (X.gp η x) (X.gp η y) := by
  unfold gp; rw [clampZ_min, min_sub_sub_right]

def gapSum (η : ℕ) (u v : Fin X.n) : ℤ :=
  ∑ g : Fin 4, ∑ h : Fin 4, mass g * mass h * min (X.gp η (X.ρ u g)) (X.gp η (X.ρ v h))

section
variable {X}
variable (hn : 0 < X.n)
include hn

theorem gapSum_eq {η : ℕ} (hη : η < X.n) (u v : Fin X.n) :
    X.gapSum η u v = X.gap η * X.dpre u (X.n - η) * X.dpre v (X.n - η) := by
  have hg : 0 < X.gap η := lt_trans (mul_pos X.G_pos X.M_pos) (gap_gt hn hη)
  have e : ∀ g h : Fin 4, mass g * mass h * min (X.gp η (X.ρ u g)) (X.gp η (X.ρ v h))
      = (if η < X.ht u g then mass g else 0) * (if η < X.ht v h then mass h else 0) * X.gap η := by
    intro g h
    rw [gp_atom hn hη, gp_atom hn hη]
    split_ifs <;> simp [min_eq_left hg.le, min_eq_right hg.le]
  unfold gapSum
  simp only [e]
  rw [← Mab_eq_dpre X hη u, ← Mab_eq_dpre X hη v]
  unfold Mab
  have e2 : ∀ g : Fin 4, (∑ h : Fin 4, ((if η < X.ht u g then mass g else 0)
      * (if η < X.ht v h then mass h else 0)) * X.gap η)
      = (if η < X.ht u g then mass g else 0)
        * (∑ h : Fin 4, if η < X.ht v h then mass h else 0) * X.gap η := by
    intro g; rw [Finset.mul_sum, Finset.sum_mul]
  simp only [e2]
  rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

/-- **Profile decomposition (8.10)-(8.12)**: `4 J_{uv}` = main-gap part + band part. -/
theorem J4_decomp {u v : Fin X.n} (huv : u ≠ v) :
    X.J4 u v = ∑ η ∈ range X.n, X.gap η * X.dpre u (X.n - η) * X.dpre v (X.n - η)
      + ∑ η ∈ range (X.n + 1), X.bandSum η u v := by
  rw [X.J4_compress hn huv]
  have hmin : ∀ g h : Fin 4, min (X.ρ u g) (X.ρ v h)
      = X.lo 0 + ∑ η ∈ range (X.n + 1), min (X.bp η (X.ρ u g)) (X.bp η (X.ρ v h))
        + ∑ η ∈ range X.n, min (X.gp η (X.ρ u g)) (X.gp η (X.ρ v h)) := by
    intro g h
    have r1 := atom_in_range hn u g
    have r2 := atom_in_range hn v h
    have := layer_decomp hn (x := min (X.ρ u g) (X.ρ v h))
      (le_min r1.1 r2.1) (le_trans (min_le_left _ _) r1.2)
    rw [this]
    simp only [bp_min, gp_min]
  simp only [hmin, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have swap3 : ∀ (F : Fin 4 → Fin 4 → ℕ → ℤ) (s : Finset ℕ),
      ∑ g : Fin 4, ∑ h : Fin 4, ∑ η ∈ s, F g h η = ∑ η ∈ s, ∑ g : Fin 4, ∑ h : Fin 4, F g h η := by
    intro F s
    calc ∑ g : Fin 4, ∑ h : Fin 4, ∑ η ∈ s, F g h η
          = ∑ g : Fin 4, ∑ η ∈ s, ∑ h : Fin 4, F g h η :=
            Finset.sum_congr rfl (fun g _ => Finset.sum_comm)
      _ = ∑ η ∈ s, ∑ g : Fin 4, ∑ h : Fin 4, F g h η := Finset.sum_comm
  have h0 : ∑ g : Fin 4, ∑ h : Fin 4, mass g * mass h * X.lo 0 = 0 := by
    simp [Fin.sum_univ_four, mass]; ring
  have hb : ∑ g : Fin 4, ∑ h : Fin 4, ∑ η ∈ range (X.n + 1),
      mass g * mass h * min (X.bp η (X.ρ u g)) (X.bp η (X.ρ v h))
      = ∑ η ∈ range (X.n + 1), X.bandSum η u v := by
    rw [swap3 (fun g h η => mass g * mass h * min (X.bp η (X.ρ u g)) (X.bp η (X.ρ v h)))]
    rfl
  have hgp : ∑ g : Fin 4, ∑ h : Fin 4, ∑ η ∈ range X.n,
      mass g * mass h * min (X.gp η (X.ρ u g)) (X.gp η (X.ρ v h))
      = ∑ η ∈ range X.n, X.gap η * X.dpre u (X.n - η) * X.dpre v (X.n - η) := by
    rw [swap3 (fun g h η => mass g * mass h * min (X.gp η (X.ρ u g)) (X.gp η (X.ρ v h)))]
    refine Finset.sum_congr rfl (fun η hη => ?_)
    exact gapSum_eq hn (Finset.mem_range.mp hη) u v
  rw [h0, hb, hgp]; ring

end

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 7. The canonical objective on anchor-early sets -/

/-- tardy pair coefficient of state jobs -/
def τ (s t : SJ X.n) : ℤ := min (X.pS t * X.wLS s) (X.pS s * X.wLS t)

/-- an instance agreeing with the construction on all data except possibly the anchor's
tardiness weight -/
structure Agrees (I : Inst (Job X.n)) : Prop where
  hp : ∀ j, I.p j = X.pJ j
  hwE : ∀ j, I.wE j = X.wEJ j
  hwL : ∀ s, I.wL (Job.st s) = X.wLS s

theorem agrees_pre : X.Agrees X.preInst := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
theorem agrees_inst : X.Agrees X.inst := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem pairsum_job (F : Job X.n → Job X.n → ℤ) :
    (∑ i : Job X.n, ∑ j : Job X.n, if i < j then F i j else 0)
      = ∑ t : SJ X.n, F Job.anchor (Job.st t)
        + ∑ s : SJ X.n, ∑ t : SJ X.n, if encS s < encS t then F (Job.st s) (Job.st t) else 0 := by
  rw [Job.sum_job]
  simp only [Job.sum_job (F := fun j => if Job.anchor < j then F Job.anchor j else 0),
    Job.sum_job (F := fun j => if Job.st _ < j then F (Job.st _) j else 0)]
  simp only [lt_irrefl, ite_false, zero_add, Job.anchor_lt_st, ite_true]
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have : ¬ (Job.st s : Job X.n) < Job.anchor := not_lt.mpr (Job.anchor_lt_st s).le
  simp only [this, ite_false, zero_add]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [Job.st_lt_st]

theorem wES_lt (s : SJ X.n) : X.wES s < X.pS s * (1 + X.rmax) := by
  unfold wES
  have := X.rS_le_rmax s
  have := X.pS_pos s
  nlinarith

/-- **Formula (*)**: the canonical objective of an early set containing the anchor. -/
theorem Φ_anchor_early {I : Inst (Job X.n)} (hI : X.Agrees I) {E : Finset (Job X.n)}
    (hE : Job.anchor ∈ E) :
    I.Φ E = ∑ s : SJ X.n, (if Job.st s ∈ E then X.H * X.wES s else 0)
      + ∑ s : SJ X.n, ∑ t : SJ X.n, (if encS s < encS t then
          ((if Job.st s ∈ E ∧ Job.st t ∈ E then X.α s t else 0)
            + (if Job.st s ∉ E ∧ Job.st t ∉ E then X.τ s t else 0)) else 0)
      + ∑ s : SJ X.n, (if Job.st s ∈ E then 0 else X.pS s * X.wLS s) := by
  unfold Inst.Φ
  rw [X.pairsum_job (fun i j => (if i ∈ E ∧ j ∈ E then I.eP i j else 0)
    + (if i ∉ E ∧ j ∉ E then I.tP i j else 0))]
  rw [Job.sum_job (F := fun i => if i ∈ E then 0 else I.p i * I.wL i)]
  simp only [hE, ite_true, zero_add, true_and, not_true_eq_false, false_and, ite_false, add_zero]
  have hpst : ∀ s, I.p (Job.st s) = X.pS s := fun s => by rw [hI.hp]; rfl
  have hwEst : ∀ s, I.wE (Job.st s) = X.wES s := fun s => by rw [hI.hwE]; rfl
  have hpa : I.p Job.anchor = X.H := by rw [hI.hp]; rfl
  have hwEa : I.wE Job.anchor = X.H * (1 + X.rmax) := by rw [hI.hwE]; rfl
  have heP : ∀ s, I.eP Job.anchor (Job.st s) = X.H * X.wES s := by
    intro s
    unfold Inst.eP
    rw [hpst, hwEa, hpa, hwEst]
    apply min_eq_right
    have := X.wES_lt s
    have := X.H_pos
    nlinarith
  have heP' : ∀ s t, I.eP (Job.st s) (Job.st t) = X.α s t := by
    intro s t; unfold Inst.eP α; rw [hpst, hpst, hwEst, hwEst]
  have htP' : ∀ s t, I.tP (Job.st s) (Job.st t) = X.τ s t := by
    intro s t; unfold Inst.tP τ; rw [hpst, hpst, hI.hwL, hI.hwL]
  simp only [heP, heP', htP', hpst, hI.hwL]

theorem Φ_pre_eq_inst {E : Finset (Job X.n)} (hE : Job.anchor ∈ E) :
    X.preInst.Φ E = X.inst.Φ E := by
  rw [X.Φ_anchor_early X.agrees_pre hE, X.Φ_anchor_early X.agrees_inst hE]

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 8. Quadratic bookkeeping over state jobs (all in `ℚ`) -/

/-- pair sums over the fixed numbering of state jobs -/
def psum (g : SJ X.n → SJ X.n → ℚ) : ℚ :=
  ∑ s : SJ X.n, ∑ t : SJ X.n, if encS s < encS t then g s t else 0

theorem psum_eq_half (g : SJ X.n → SJ X.n → ℚ) (hg : ∀ s t, g s t = g t s) :
    X.psum g = (1/2) * (∑ s : SJ X.n, ∑ t : SJ X.n, g s t) - (1/2) * ∑ s : SJ X.n, g s s := by
  unfold psum
  have hswap : (∑ s : SJ X.n, ∑ t : SJ X.n, if encS t < encS s then g s t else 0)
      = ∑ s : SJ X.n, ∑ t : SJ X.n, if encS s < encS t then g s t else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
    rw [hg]
  have htri : (∑ s : SJ X.n, ∑ t : SJ X.n, g s t)
      = (∑ s : SJ X.n, ∑ t : SJ X.n, if encS s < encS t then g s t else 0)
        + (∑ s : SJ X.n, ∑ t : SJ X.n, if encS t < encS s then g s t else 0)
        + ∑ s : SJ X.n, g s s := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [← Finset.sum_add_distrib]
    rw [show g s s = ∑ t : SJ X.n, if t = s then g s t else 0 by simp]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : t = s
    · subst h; simp
    · have hne : encS s ≠ encS t := fun e => h (Job.encS_inj e).symm
      rcases lt_or_gt_of_ne hne with h1 | h1
      · simp [h, h1, not_lt.mpr h1.le]
      · simp [h, h1, not_lt.mpr h1.le]
  rw [hswap] at htri
  linarith

/-- factorisation of a block-kernel double sum -/
theorem sum_block2 (c : Fin X.n → Fin X.n → ℚ) (z : SJ X.n → ℚ) :
    ∑ s : SJ X.n, ∑ t : SJ X.n, c s.1 t.1 * z s * z t
      = ∑ u, ∑ v, c u v * (∑ a : Fin 4 × Bool, z (u, a)) * (∑ b : Fin 4 × Bool, z (v, b)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp_rw [Fintype.sum_prod_type (f := fun t : SJ X.n => c u t.1 * z (u, _) * z t)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => by ring)

theorem sum_block1 (c : Fin X.n → ℚ) (z : SJ X.n → ℚ) :
    ∑ s : SJ X.n, c s.1 * z s = ∑ u, c u * ∑ a : Fin 4 × Bool, z (u, a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]

/-! ### tardiness ratios: the dominant layer and the offsets -/

theorem sS_strict (_hn : 0 < X.n) {s t : SJ X.n} (h : s.1 < t.1) : X.sS t < X.sS s := by
  unfold sS
  have hL := X.L_sub s.1 t.1
  have h1 : (s.1 : ℤ) < t.1 := by exact_mod_cast h
  have hH := X.H_gt_etamax
  have hs := X.abs_eta_le_etamax s.1
  have ht := X.abs_eta_le_etamax t.1
  have hH0 := X.H_pos
  have e1 := abs_le.mp hs
  have e2 := abs_le.mp ht
  nlinarith

theorem min_sS (hn : 0 < X.n) (s t : SJ X.n) :
    min (X.sS s) (X.sS t) = X.H * X.K s.1 t.1 + X.etabar s t := by
  unfold etabar K
  rcases lt_trichotomy s.1 t.1 with h | h | h
  · have hst := X.sS_strict hn h
    have hL : X.L t.1 ≤ X.L s.1 := by
      have := X.L_sub s.1 t.1; have : (s.1 : ℤ) < t.1 := by exact_mod_cast h
      linarith
    rw [min_eq_right hst.le, min_eq_right hL, ite_eq_right (ne_of_lt h), max_eq_right h.le]
    rfl
  · rw [ite_eq_left h]
    have : X.sS s = X.sS t := by unfold sS; rw [h]
    rw [this, min_self, h, min_self]; unfold sS; rfl
  · have hst := X.sS_strict hn h
    have hL : X.L s.1 ≤ X.L t.1 := by
      have := X.L_sub t.1 s.1; have : (t.1 : ℤ) < s.1 := by exact_mod_cast h
      linarith
    rw [min_eq_left hst.le, min_eq_left hL, ite_eq_right (ne_of_gt h), max_eq_left h.le]
    rfl

theorem τ_eq (hn : 0 < X.n) (s t : SJ X.n) :
    X.τ s t = X.pS s * X.pS t * (X.H * X.K s.1 t.1 + X.etabar s t) := by
  unfold τ wLS
  rw [← X.min_sS hn s t]
  have hps := X.pS_pos s; have hpt := X.pS_pos t
  rw [show X.pS t * (X.pS s * X.sS s) = (X.pS s * X.pS t) * X.sS s by ring,
    show X.pS s * (X.pS t * X.sS t) = (X.pS s * X.pS t) * X.sS t by ring]
  rw [mul_min_of_nonneg _ _ (by positivity)]

theorem etabar_symm (s t : SJ X.n) : X.etabar s t = X.etabar t s := by
  unfold etabar
  by_cases h : s.1 = t.1
  · rw [ite_eq_left h, ite_eq_left h.symm, h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), max_comm]

theorem etabar_self (s : SJ X.n) : X.etabar s s = X.eta s.1 := by simp [etabar]

theorem K_symm (u v : Fin X.n) : X.K u v = X.K v u := by unfold K; rw [min_comm]
theorem K_self (u : Fin X.n) : X.K u u = X.L u := by unfold K; rw [min_self]
theorem τ_symm (s t : SJ X.n) : X.τ s t = X.τ t s := by unfold τ; rw [min_comm]
theorem τ_self (s : SJ X.n) : X.τ s s = X.pS s * X.wLS s := by unfold τ; rw [min_self]

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ### the load-lock decomposition (Lemma I.15) -/

theorem psum_add (f g : SJ X.n → SJ X.n → ℚ) :
    X.psum (fun s t => f s t + g s t) = X.psum f + X.psum g := by
  unfold psum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs <;> ring

theorem psum_smul (c : ℚ) (f : SJ X.n → SJ X.n → ℚ) :
    X.psum (fun s t => c * f s t) = c * X.psum f := by
  unfold psum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs <;> ring

theorem psum_congr {f g : SJ X.n → SJ X.n → ℚ} (h : ∀ s t, f s t = g s t) :
    X.psum f = X.psum g := by
  unfold psum; simp only [h]

/-- tardy load of block `u` under early indicators `x` -/
def bq (x : SJ X.n → ℚ) (u : Fin X.n) : ℚ := ∑ a : Fin 4 × Bool, (1 - x (u, a)) * X.pS (u, a)
def qq (x : SJ X.n → ℚ) (u : Fin X.n) : ℚ := ∑ a : Fin 4 × Bool, (1 - x (u, a)) * (X.pS (u, a) : ℚ) ^ 2
def Qsq (u : Fin X.n) : ℚ := ∑ a : Fin 4 × Bool, (X.pS (u, a) : ℚ) ^ 2

/-- the canonical objective of an anchor-early set, as a polynomial in its early indicators -/
def phiQ (x : SJ X.n → ℚ) : ℚ :=
  ∑ s, x s * ((X.H : ℚ) * X.wES s)
    + X.psum (fun s t => x s * x t * X.α s t + (1 - x s) * (1 - x t) * X.τ s t)
    + ∑ s, (1 - x s) * ((X.pS s : ℚ) * X.wLS s)

/-- the residual `R₀` of Lemma I.15 -/
def R0 (x : SJ X.n → ℚ) : ℚ :=
  X.psum (fun s t => x s * x t * X.α s t)
    + X.psum (fun s t => (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.etabar s t))
    + ∑ s, (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1)

/-- the assignment-independent constant of Lemma I.15 -/
def K0 : ℚ := (X.H : ℚ) * ∑ u, (2 * (X.f u : ℚ) * X.β u + X.lam u * X.Qsq u)
  - ((X.H : ℚ) / 2) * ∑ u, ∑ v, (X.K u v : ℚ) * X.β u * X.β v

/-- the load-lock quadratic `(b - β)ᵀ K (b - β)` -/
def lockQ (x : SJ X.n → ℚ) : ℚ :=
  ∑ u, ∑ v, (X.K u v : ℚ) * (X.bq x u - X.β u) * (X.bq x v - X.β v)

theorem sum_slot_pS_q (u : Fin X.n) : ∑ a : Fin 4 × Bool, (X.pS (u, a) : ℚ) = 2 * X.β u := by
  have := X.sum_pS u; exact_mod_cast this

/-- **Lemma I.15, exact form**: on anchor-early sets, the objective is a constant plus the
dominant load-lock penalty `(H/2)(b-β)ᵀK(b-β)` plus the residual `R₀`. -/
theorem phiQ_decomp (hn : 0 < X.n) (x : SJ X.n → ℚ) (hx : ∀ s, x s = 0 ∨ x s = 1) :
    X.phiQ x = X.K0 + ((X.H : ℚ) / 2) * X.lockQ x + X.R0 x := by
  have hy2 : ∀ s, (1 - x s) * (1 - x s) = 1 - x s := by
    intro s; rcases hx s with h | h <;> rw [h] <;> ring
  -- split the tardy pair coefficient
  have hτ : ∀ s t, (X.τ s t : ℚ) = (X.H : ℚ) * ((X.pS s : ℚ) * X.pS t * X.K s.1 t.1)
      + (X.pS s : ℚ) * X.pS t * X.etabar s t := by
    intro s t; rw [X.τ_eq hn]; push_cast; ring
  have hself : ∀ s, (X.pS s : ℚ) * X.wLS s
      = (X.H : ℚ) * ((X.pS s : ℚ) ^ 2 * X.L s.1) + (X.pS s : ℚ) ^ 2 * X.eta s.1 := by
    intro s; unfold wLS sS; push_cast; ring
  -- the dominant tardy pair part
  have hTK : X.psum (fun s t => (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.K s.1 t.1))
      = (1/2) * ∑ u, ∑ v, (X.K u v : ℚ) * X.bq x u * X.bq x v
        - (1/2) * ∑ u, (X.L u : ℚ) * X.qq x u := by
    rw [X.psum_eq_half _ (by intro s t; rw [X.K_symm]; ring)]
    have e1 : ∑ s : SJ X.n, ∑ t : SJ X.n, (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.K s.1 t.1)
        = ∑ u, ∑ v, (X.K u v : ℚ) * X.bq x u * X.bq x v := by
      have := X.sum_block2 (fun u v => (X.K u v : ℚ)) (fun s => (1 - x s) * X.pS s)
      calc _ = ∑ s : SJ X.n, ∑ t : SJ X.n,
              (X.K s.1 t.1 : ℚ) * ((1 - x s) * X.pS s) * ((1 - x t) * X.pS t) :=
            Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => by ring))
        _ = _ := this
    have e2 : ∑ s : SJ X.n, (1 - x s) * (1 - x s) * ((X.pS s : ℚ) * X.pS s * X.K s.1 s.1)
        = ∑ u, (X.L u : ℚ) * X.qq x u := by
      have := X.sum_block1 (fun u => (X.L u : ℚ)) (fun s => (1 - x s) * (X.pS s : ℚ) ^ 2)
      calc _ = ∑ s : SJ X.n, (X.L s.1 : ℚ) * ((1 - x s) * (X.pS s : ℚ) ^ 2) :=
            Finset.sum_congr rfl (fun s _ => by rw [hy2, X.K_self]; ring)
        _ = _ := this
    rw [e1, e2]
  -- the anchor part
  have hA : ∑ s, x s * ((X.H : ℚ) * X.wES s)
      = (X.H : ℚ) * ∑ u, ((X.f u : ℚ) * (2 * X.β u - X.bq x u) + X.lam u * (X.Qsq u - X.qq x u)) := by
    have hw : ∀ s, x s * ((X.H : ℚ) * X.wES s)
        = (X.H : ℚ) * ((X.f s.1 : ℚ) * (x s * X.pS s) + (X.lam s.1 : ℚ) * (x s * (X.pS s : ℚ) ^ 2)) := by
      intro s; unfold wES rS; push_cast; ring
    simp only [hw]
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    rw [X.sum_block1 (fun u => (X.f u : ℚ)) (fun s => x s * X.pS s),
      X.sum_block1 (fun u => (X.lam u : ℚ)) (fun s => x s * (X.pS s : ℚ) ^ 2)]
    rw [← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have h1 : ∑ a : Fin 4 × Bool, x (u, a) * (X.pS (u, a) : ℚ) = 2 * X.β u - X.bq x u := by
      rw [← X.sum_slot_pS_q u]; unfold bq; rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun a _ => by ring)
    have h2 : ∑ a : Fin 4 × Bool, x (u, a) * (X.pS (u, a) : ℚ) ^ 2 = X.Qsq u - X.qq x u := by
      unfold Qsq qq; rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun a _ => by ring)
    rw [h1, h2]
  -- the quadratic form expansion
  have hf : ∀ u, (X.f u : ℚ) = ∑ v, (X.K u v : ℚ) * X.β v := by
    intro u; unfold f; push_cast; rfl
  have hL : X.lockQ x = ∑ u, ∑ v, (X.K u v : ℚ) * X.bq x u * X.bq x v
      - 2 * ∑ u, X.bq x u * (X.f u : ℚ) + ∑ u, ∑ v, (X.K u v : ℚ) * X.β u * X.β v := by
    unfold lockQ
    have e : ∀ u v, (X.K u v : ℚ) * (X.bq x u - X.β u) * (X.bq x v - X.β v)
        = (X.K u v : ℚ) * X.bq x u * X.bq x v - X.bq x u * ((X.K u v : ℚ) * X.β v)
          - X.bq x v * ((X.K v u : ℚ) * X.β u) + (X.K u v : ℚ) * X.β u * X.β v := by
      intro u v; rw [X.K_symm v u]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun u v => X.bq x v * ((X.K v u : ℚ) * X.β u))]
    simp only [← Finset.mul_sum, ← hf]
    ring
  -- assemble
  unfold phiQ R0 K0
  rw [X.psum_congr (f := fun s t => x s * x t * X.α s t + (1 - x s) * (1 - x t) * X.τ s t)
    (g := fun s t => x s * x t * X.α s t
      + ((X.H : ℚ) * ((1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.K s.1 t.1))
        + (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.etabar s t)))
    (by intro s t; rw [hτ]; ring)]
  rw [X.psum_add, X.psum_add, X.psum_smul, hTK, hA]
  have hS : ∑ s, (1 - x s) * ((X.pS s : ℚ) * X.wLS s)
      = (X.H : ℚ) * ∑ u, (X.L u : ℚ) * X.qq x u
        + ∑ s, (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1) := by
    have e : ∀ s, (1 - x s) * ((X.pS s : ℚ) * X.wLS s)
        = (X.H : ℚ) * ((X.L s.1 : ℚ) * ((1 - x s) * (X.pS s : ℚ) ^ 2))
          + (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1) := by
      intro s; rw [hself]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 2
    rw [X.sum_block1 (fun u => (X.L u : ℚ)) (fun s => (1 - x s) * (X.pS s : ℚ) ^ 2)]
    rfl
  rw [hS, hL]
  -- final linear bookkeeping over block sums
  have hLl : ∀ u, (X.L u : ℚ) = 2 * X.lam u := by intro u; unfold L; push_cast; ring
  have s1 : ∑ u, ((X.f u : ℚ) * (2 * X.β u - X.bq x u) + X.lam u * (X.Qsq u - X.qq x u))
      = ∑ u, (2 * (X.f u : ℚ) * X.β u + X.lam u * X.Qsq u) - ∑ u, X.bq x u * (X.f u : ℚ)
        - ∑ u, (X.lam u : ℚ) * X.qq x u := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => by ring)
  have s2 : ∑ u, (X.L u : ℚ) * X.qq x u = 2 * ∑ u, (X.lam u : ℚ) * X.qq x u := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun u _ => by rw [hLl]; ring)
  rw [s1, s2]
  ring

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 9. The global load lock (Lemma I.15) and the anchor gate -/

/-- early indicators of an early set -/
def xE (E : Finset (Job X.n)) (s : SJ X.n) : ℚ := if Job.st s ∈ E then 1 else 0

theorem xE_01 (E : Finset (Job X.n)) (s : SJ X.n) : X.xE E s = 0 ∨ X.xE E s = 1 := by
  unfold xE; split_ifs <;> simp

theorem Φ_eq_phiQ {I : Inst (Job X.n)} (hI : X.Agrees I) {E : Finset (Job X.n)}
    (hE : Job.anchor ∈ E) : (I.Φ E : ℚ) = X.phiQ (X.xE E) := by
  rw [X.Φ_anchor_early hI hE]
  unfold phiQ psum xE
  push_cast
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl (fun s _ => ?_)
      split_ifs <;> ring
    · refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
      by_cases h : encS s < encS t
      · simp only [h, ite_true]
        by_cases hs : Job.st s ∈ E <;> by_cases ht : Job.st t ∈ E <;> simp [hs, ht]
      · simp [h]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs <;> ring

/-! ### positive definiteness of the minimum kernel -/

/-- `L` extended by `0` beyond the last block -/
def Lnat (k : ℕ) : ℤ := if k < X.n then 2 * (X.G + X.n - k) else 0

theorem K_eq_Lnat (u v : Fin X.n) : X.K u v = X.Lnat (max u.val v.val) := by
  unfold K Lnat L lam
  have hm : max u.val v.val < X.n := max_lt u.isLt v.isLt
  rw [ite_eq_left hm]
  rcases le_total u.val v.val with h | h
  · have : (u : ℤ) ≤ v := by exact_mod_cast h
    rw [max_eq_right h, min_eq_right (by linarith)]
  · have : (v : ℤ) ≤ u := by exact_mod_cast h
    rw [max_eq_left h, min_eq_left (by linarith)]

theorem Lnat_step (k : ℕ) (hk : k < X.n) : 2 ≤ X.Lnat k - X.Lnat (k + 1) := by
  unfold Lnat
  rw [ite_eq_left hk]
  by_cases h : k + 1 < X.n
  · rw [ite_eq_left h]; push_cast; linarith
  · rw [ite_eq_right h]; have := X.G_pos; linarith

/-- telescoping: `L_m = Σ_{k ≥ m} (L_k - L_{k+1})` -/
theorem Lnat_telescope (m : ℕ) (hm : m < X.n) :
    X.Lnat m = ∑ k ∈ range X.n, if m ≤ k then X.Lnat k - X.Lnat (k + 1) else 0 := by
  set F : ℕ → ℤ := fun k => if m ≤ k then X.Lnat k else X.Lnat m with hF
  have h1 : ∀ k, (if m ≤ k then X.Lnat k - X.Lnat (k + 1) else 0) = F k - F (k + 1) := by
    intro k
    simp only [hF]
    by_cases h : m ≤ k
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right h]
      by_cases h' : m ≤ k + 1
      · rw [ite_eq_left h', show k + 1 = m by omega]; ring
      · rw [ite_eq_right h']; ring
  simp only [h1]
  rw [Finset.sum_range_sub']
  have hF0 : F 0 = X.Lnat m := by
    simp only [hF]; split_ifs with h
    · have : m = 0 := by omega
      rw [this]
    · rfl
  have hFn : F X.n = 0 := by
    simp only [hF]; rw [ite_eq_left hm.le]; unfold Lnat; rw [ite_eq_right (lt_irrefl _)]
  rw [hF0, hFn]; ring

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-- prefix-square representation (8.24) of the minimum-kernel quadratic form -/
theorem quad_prefix (y : Fin X.n → ℚ) :
    ∑ u, ∑ v, (X.K u v : ℚ) * y u * y v
      = ∑ k ∈ range X.n, ((X.Lnat k - X.Lnat (k + 1) : ℤ) : ℚ)
          * (∑ u : Fin X.n, if u.val ≤ k then y u else 0) ^ 2 := by
  have hK : ∀ u v : Fin X.n, (X.K u v : ℚ) = ∑ k ∈ range X.n,
      if u.val ≤ k ∧ v.val ≤ k then ((X.Lnat k - X.Lnat (k + 1) : ℤ) : ℚ) else 0 := by
    intro u v
    rw [X.K_eq_Lnat, X.Lnat_telescope _ (max_lt u.isLt v.isLt)]
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [max_le_iff]
  simp only [hK, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hu : u.val ≤ k <;> by_cases hv : v.val ≤ k <;> simp [hu, hv]
  ring

/-- **Positive definiteness**: every nonzero integer load error costs at least `2`. -/
theorem quad_ge_two (y : Fin X.n → ℚ) (hint : ∀ u, ∃ z : ℤ, y u = z) (hne : ∃ u, y u ≠ 0) :
    2 ≤ ∑ u, ∑ v, (X.K u v : ℚ) * y u * y v := by
  rw [X.quad_prefix]
  set S := univ.filter (fun u : Fin X.n => y u ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨u, hu⟩ := hne; exact ⟨u, by simp [hS, hu]⟩
  set u0 := S.min' hSne
  have hu0 : u0 ∈ S := Finset.min'_mem S hSne
  have hyu0 : y u0 ≠ 0 := by simpa [hS] using hu0
  have hbelow : ∀ u : Fin X.n, u.val < u0.val → y u = 0 := by
    intro u hu
    by_contra h
    have : u ∈ S := by simp [hS, h]
    have := Finset.min'_le S u this
    have : u0.val ≤ u.val := this
    omega
  have hz : (∑ u : Fin X.n, if u.val ≤ u0.val then y u else 0) = y u0 := by
    rw [Finset.sum_eq_single u0]
    · simp
    · intro b _ hb
      by_cases h : b.val ≤ u0.val
      · have : b.val < u0.val := lt_of_le_of_ne h (fun e => hb (Fin.ext e))
        simp [h, hbelow b this]
      · simp [h]
    · intro h; exact absurd (mem_univ u0) h
  have hsq : 1 ≤ (y u0) ^ 2 := by
    obtain ⟨z, hz'⟩ := hint u0
    rw [hz'] at hyu0 ⊢
    have : z ≠ 0 := by exact_mod_cast hyu0
    have : 1 ≤ z ^ 2 := by
      have := Int.one_le_abs this
      nlinarith [sq_abs z]
    exact_mod_cast this
  have hterm : ∀ k ∈ range X.n, 0 ≤ ((X.Lnat k - X.Lnat (k + 1) : ℤ) : ℚ)
      * (∑ u : Fin X.n, if u.val ≤ k then y u else 0) ^ 2 := by
    intro k hk
    have := X.Lnat_step k (Finset.mem_range.mp hk)
    have : (0:ℚ) ≤ ((X.Lnat k - X.Lnat (k + 1) : ℤ) : ℚ) := by exact_mod_cast (by linarith)
    positivity
  have := Finset.single_le_sum hterm (Finset.mem_range.mpr u0.isLt)

  rw [hz] at this
  have hc : (2:ℚ) ≤ ((X.Lnat u0.val - X.Lnat (u0.val + 1) : ℤ) : ℚ) := by
    exact_mod_cast X.Lnat_step u0.val u0.isLt
  nlinarith

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

theorem psum_mono {f g : SJ X.n → SJ X.n → ℚ} (h : ∀ s t, f s t ≤ g s t) :
    X.psum f ≤ X.psum g := by
  unfold psum
  refine Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => ?_))
  split_ifs
  · exact h s t
  · exact le_refl 0

theorem psum_sub (f g : SJ X.n → SJ X.n → ℚ) :
    X.psum (fun s t => f s t - g s t) = X.psum f - X.psum g := by
  unfold psum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs <;> ring

/-- lower envelope of the residual `R₀` -/
def Rlo : ℚ := X.psum (fun s t => min 0 ((X.pS s : ℚ) * X.pS t * X.etabar s t))
  + ∑ s, min 0 ((X.pS s : ℚ) ^ 2 * X.eta s.1)

theorem U_sub_one : ((X.U : ℚ) - 1) = X.psum (fun s t => (X.α s t : ℚ))
    + ∑ s, |(X.pS s : ℚ) ^ 2 * X.eta s.1|
    + X.psum (fun s t => |(X.pS s : ℚ) * X.pS t * X.etabar s t|) := by
  unfold U psum
  push_cast
  have e1 : ∀ s : SJ X.n, |(X.eta s.1 : ℚ)| * (X.pS s : ℚ) ^ 2 = |(X.pS s : ℚ) ^ 2 * X.eta s.1| := by
    intro s; rw [abs_mul, abs_of_nonneg (by positivity : (0:ℚ) ≤ (X.pS s : ℚ) ^ 2)]; ring
  have e2 : ∀ s t : SJ X.n, |(X.etabar s t : ℚ)| * (X.pS s : ℚ) * X.pS t
      = |(X.pS s : ℚ) * X.pS t * X.etabar s t| := by
    intro s t
    have hs : (0:ℚ) ≤ X.pS s := by exact_mod_cast (X.pS_pos s).le
    have ht : (0:ℚ) ≤ X.pS t := by exact_mod_cast (X.pS_pos t).le
    rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]; ring
  simp only [e1, e2]
  ring

theorem zz_bounds (z c : ℚ) (hz : z = 0 ∨ z = 1) : min 0 c ≤ z * c ∧ z * c ≤ min 0 c + |c| := by
  rcases hz with rfl | rfl
  · simp only [zero_mul]
    constructor
    · exact min_le_left _ _
    · rcases le_total 0 c with h | h
      · rw [min_eq_left h, abs_of_nonneg h]; linarith
      · rw [min_eq_right h, abs_of_nonpos h]; linarith
  · simp only [one_mul]
    constructor
    · exact min_le_right _ _
    · rcases le_total 0 c with h | h
      · rw [min_eq_left h, abs_of_nonneg h]; linarith
      · rw [min_eq_right h, abs_of_nonpos h]; linarith

theorem R0_bounds (x : SJ X.n → ℚ) (hx : ∀ s, x s = 0 ∨ x s = 1) :
    X.Rlo ≤ X.R0 x ∧ X.R0 x ≤ X.Rlo + ((X.U : ℚ) - 1) := by
  have hy : ∀ s, (1 - x s) = 0 ∨ (1 - x s) = 1 := by
    intro s; rcases hx s with h | h <;> rw [h] <;> norm_num
  have hyy : ∀ s t, (1 - x s) * (1 - x t) = 0 ∨ (1 - x s) * (1 - x t) = 1 := by
    intro s t; rcases hy s with h | h <;> rcases hy t with h' | h' <;> rw [h, h'] <;> norm_num
  have hxx : ∀ s t, x s * x t = 0 ∨ x s * x t = 1 := by
    intro s t; rcases hx s with h | h <;> rcases hx t with h' | h' <;> rw [h, h'] <;> norm_num
  have hα : ∀ s t, (0:ℚ) ≤ X.α s t := fun s t => by exact_mod_cast (X.α_pos s t).le
  unfold R0 Rlo
  rw [X.U_sub_one]
  constructor
  · have a1 : 0 ≤ X.psum (fun s t => x s * x t * X.α s t) := by
      have := X.psum_mono (f := fun _ _ => (0:ℚ)) (g := fun s t => x s * x t * X.α s t)
        (fun s t => by rcases hxx s t with h | h <;> rw [h] <;> simp [hα s t])
      unfold psum at this ⊢; simpa using this
    have a2 := X.psum_mono (f := fun s t => min 0 ((X.pS s : ℚ) * X.pS t * X.etabar s t))
      (g := fun s t => (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.etabar s t))
      (fun s t => (zz_bounds _ _ (hyy s t)).1)
    have a3 : ∑ s, min 0 ((X.pS s : ℚ) ^ 2 * X.eta s.1)
        ≤ ∑ s, (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1) :=
      Finset.sum_le_sum (fun s _ => (zz_bounds _ _ (hy s)).1)
    linarith
  · have a1 := X.psum_mono (f := fun s t => x s * x t * X.α s t) (g := fun s t => (X.α s t : ℚ))
      (fun s t => by rcases hxx s t with h | h <;> rw [h] <;> simp [hα s t])
    have a2 := X.psum_mono (f := fun s t => (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.etabar s t))
      (g := fun s t => min 0 ((X.pS s : ℚ) * X.pS t * X.etabar s t)
        + |(X.pS s : ℚ) * X.pS t * X.etabar s t|)
      (fun s t => (zz_bounds _ _ (hyy s t)).2)
    rw [X.psum_add] at a2
    have a3 : ∑ s, (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1)
        ≤ ∑ s, (min 0 ((X.pS s : ℚ) ^ 2 * X.eta s.1) + |(X.pS s : ℚ) ^ 2 * X.eta s.1|) :=
      Finset.sum_le_sum (fun s _ => (zz_bounds _ _ (hy s)).2)
    rw [Finset.sum_add_distrib] at a3
    linarith

/-! ### coded early sets -/

theorem mem_codedE_anchor (σ : Fin X.n → Bool) : Job.anchor ∈ X.codedE σ := by
  simp [codedE, Job.elim_anchor]

theorem mem_codedE_st (σ : Fin X.n → Bool) (s : SJ X.n) :
    Job.st s ∈ X.codedE σ ↔ sgn (σ s.1) * eps s.2.1 s.2.2 = 1 := by
  simp [codedE, Job.elim_st]

/-- `±1` as a rational -/
def sgnQ (b : Bool) : ℚ := if b then 1 else -1

theorem sgnQ_sq (b : Bool) : sgnQ b ^ 2 = 1 := by cases b <;> simp [sgnQ]
theorem sgn_cast (b : Bool) : ((sgn b : ℤ) : ℚ) = sgnQ b := by cases b <;> simp [sgn, sgnQ]

theorem xE_coded (σ : Fin X.n → Bool) (s : SJ X.n) :
    X.xE (X.codedE σ) s = (1 + sgnQ (σ s.1) * eps s.2.1 s.2.2) / 2 := by
  unfold xE
  by_cases hm : Job.st s ∈ X.codedE σ
  · rw [ite_eq_left hm]
    rw [mem_codedE_st] at hm
    rcases eps_cases s.2.1 s.2.2 with h | h <;> cases hσ : σ s.1 <;>
      simp_all [sgn, sgnQ]
  · rw [ite_eq_right hm]
    rw [mem_codedE_st] at hm
    rcases eps_cases s.2.1 s.2.2 with h | h <;> cases hσ : σ s.1 <;>
      simp_all [sgn, sgnQ]

theorem bq_coded (σ : Fin X.n → Bool) (u : Fin X.n) : X.bq (X.xE (X.codedE σ)) u = X.β u := by
  unfold bq
  simp only [xE_coded]
  have h1 := X.sum_slot_pS_q u
  have h2 : ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ) * X.pS (u, a) = 0 := by
    have := X.sum_eps_pS u; exact_mod_cast this
  have : ∑ a : Fin 4 × Bool, (1 - (1 + sgnQ (σ u) * eps a.1 a.2) / 2) * (X.pS (u, a) : ℚ)
      = (1/2) * ∑ a : Fin 4 × Bool, (X.pS (u, a) : ℚ)
        - (sgnQ (σ u) / 2) * ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ) * X.pS (u, a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => by ring)
  rw [this, h1, h2]; ring

/-- **Lemma I.15 (global load lock).** With the anchor early, any early set whose tardy block
loads differ from `β` costs strictly more than the coded benchmark set. -/
theorem load_lock (hn : 0 < X.n) {E : Finset (Job X.n)} (hE : Job.anchor ∈ E)
    (hb : ∃ u, X.bq (X.xE E) u ≠ X.β u) :
    X.inst.Φ (X.codedE (fun _ => true)) < X.inst.Φ E := by
  have h1 := X.Φ_eq_phiQ X.agrees_inst hE
  have h2 := X.Φ_eq_phiQ X.agrees_inst (X.mem_codedE_anchor (fun _ => true))
  rw [X.phiQ_decomp hn _ (X.xE_01 E)] at h1
  rw [X.phiQ_decomp hn _ (X.xE_01 _)] at h2
  have hl2 : X.lockQ (X.xE (X.codedE (fun _ => true))) = 0 := by
    unfold lockQ; simp [bq_coded]
  have hl1 : 2 ≤ X.lockQ (X.xE E) := by
    unfold lockQ
    apply X.quad_ge_two (fun u => X.bq (X.xE E) u - X.β u)
    · intro u
      refine ⟨(∑ a : Fin 4 × Bool, (if Job.st (u, a) ∈ E then 0 else X.pS (u, a))) - X.β u, ?_⟩
      unfold bq xE; push_cast
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      split_ifs <;> ring
    · obtain ⟨u, hu⟩ := hb; exact ⟨u, sub_ne_zero.mpr hu⟩
  have r1 := (X.R0_bounds (X.xE E) (X.xE_01 E)).1
  have r2 := (X.R0_bounds _ (X.xE_01 (X.codedE (fun _ => true)))).2
  have hH : (X.U : ℚ) + 2 ≤ X.H := by
    have := X.etamax_nonneg; unfold H; push_cast; linarith [(by exact_mod_cast this : (0:ℚ) ≤ X.etamax)]
  have hHpos : (0:ℚ) < X.H := by exact_mod_cast X.H_pos
  have key : (X.inst.Φ (X.codedE (fun _ => true)) : ℚ) < X.inst.Φ E := by
    rw [h1, h2, hl2]
    nlinarith
  exact_mod_cast key

/-- **Anchor gate (8.25).** An early set with the anchor tardy costs more than `C⋆`. -/
theorem anchor_gate {E : Finset (Job X.n)} (hE : Job.anchor ∉ E) :
    X.Cstar < X.inst.Φ E := by
  -- the anchor's own tardy term
  have hself : X.inst.p Job.anchor * X.inst.wL Job.anchor ≤ X.inst.Φ E := by
    rw [Inst.Φ_split]
    have h1 : 0 ≤ ∑ i, ∑ j, (if i < j then (if i ∈ E ∧ j ∈ E then X.inst.eP i j else 0) else 0) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
        split_ifs <;> first | exact le_refl 0 | exact (X.inst.eP_pos i j).le))
    have h2 : 0 ≤ ∑ i, ∑ j, (if i < j then (if i ∉ E ∧ j ∉ E then X.inst.tP i j else 0) else 0) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
        split_ifs <;> first | exact le_refl 0 | exact (X.inst.tP_pos i j).le))
    have h3 : X.inst.p Job.anchor * X.inst.wL Job.anchor
        ≤ ∑ i, (if i ∈ E then 0 else X.inst.p i * X.inst.wL i) := by
      have := Finset.single_le_sum (f := fun i => if i ∈ E then 0 else X.inst.p i * X.inst.wL i)
        (fun i _ => by
          split_ifs
          · exact le_refl 0
          · have := X.inst.hp i; have := X.inst.hwL i; positivity) (mem_univ Job.anchor)
      simpa [hE] using this
    linarith
  have hval : X.inst.p Job.anchor * X.inst.wL Job.anchor = X.H * (X.H * X.sa) := rfl
  rw [hval] at hself
  -- H² s_a > C⋆
  have hH := X.H_pos
  have hC := X.Cstar_nonneg
  have : (X.Cstar : ℚ) < (X.H : ℚ) * ((X.H : ℚ) * X.sa) := by
    unfold sa
    push_cast
    have hH2 : (0:ℚ) < (X.H : ℚ) ^ 2 := by positivity
    have hc := Int.le_ceil ((X.Cstar : ℚ) / (X.H : ℚ) ^ 2)
    have : (X.Cstar : ℚ) ≤ (X.H : ℚ) ^ 2 * ⌈(X.Cstar : ℚ) / (X.H : ℚ) ^ 2⌉ := by
      rw [div_le_iff₀ hH2] at hc; linarith
    nlinarith
  have : X.Cstar < X.H * (X.H * X.sa) := by exact_mod_cast this
  linarith

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 10. Expansion on the coded state space and the master identity (Lemma I.16) -/

/-- coded spin of a state job: `σ_v ε_i` -/
def spin (σ : Fin X.n → Bool) (s : SJ X.n) : ℚ := sgnQ (σ s.1) * eps s.2.1 s.2.2

theorem spin_sq (σ : Fin X.n → Bool) (s : SJ X.n) : X.spin σ s ^ 2 = 1 := by
  unfold spin
  have h1 := sgnQ_sq (σ s.1)
  have h2 : ((eps s.2.1 s.2.2 : ℤ) : ℚ) ^ 2 = 1 := by exact_mod_cast eps_sq s.2.1 s.2.2
  rw [mul_pow, h1, h2]; ring

theorem α_symm_q (s t : SJ X.n) : (X.α s t : ℚ) = X.α t s := by rw [X.α_symm]

/-- block expansion of a double sum over state jobs -/
theorem sum_pairs_blocks (F : SJ X.n → SJ X.n → ℚ) :
    ∑ s : SJ X.n, ∑ t : SJ X.n, F s t
      = ∑ u, ∑ v, ∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool, F (u, a) (v, b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp_rw [Fintype.sum_prod_type (f := fun t : SJ X.n => F (u, _) t)]
  rw [Finset.sum_comm]

/-- the baseline field `a⁰_v` in ordered-pair form -/
theorem a0_eq (v : Fin X.n) :
    X.a0 v = (1/4) * ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ)
      * ((∑ t : SJ X.n, (X.α (v, a) t : ℚ)) - X.α (v, a) (v, a)) := by
  unfold a0
  -- within-block part
  have hw : (∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
      if a ≠ b then (X.α (v, a) (v, b) : ℚ) * (eps a.1 a.2 + eps b.1 b.2) else 0)
      = 2 * ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ) * ∑ b : Fin 4 × Bool,
          if a ≠ b then (X.α (v, a) (v, b) : ℚ) else 0 := by
    have e : ∀ a b : Fin 4 × Bool, (if a ≠ b then (X.α (v, a) (v, b) : ℚ) * (eps a.1 a.2 + eps b.1 b.2) else 0)
        = (if a ≠ b then (eps a.1 a.2 : ℚ) * X.α (v, a) (v, b) else 0)
          + (if a ≠ b then (eps b.1 b.2 : ℚ) * X.α (v, a) (v, b) else 0) := by
      intro a b; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib]
    have hs : (∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
        if a ≠ b then (eps b.1 b.2 : ℚ) * X.α (v, a) (v, b) else 0)
        = ∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
          if a ≠ b then (eps a.1 a.2 : ℚ) * X.α (v, a) (v, b) else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [X.α_symm_q (v, b) (v, a)]
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hs, two_mul]
    have hfin : (∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
        if a ≠ b then (eps a.1 a.2 : ℚ) * X.α (v, a) (v, b) else 0)
        = ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ) * ∑ b : Fin 4 × Bool,
          if a ≠ b then (X.α (v, a) (v, b) : ℚ) else 0 := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs <;> ring
    rw [hfin]
  rw [hw]
  -- the off-block part as a sum over all `t` minus the block
  have hsplit : ∀ a : Fin 4 × Bool, (∑ t : SJ X.n, (X.α (v, a) t : ℚ)) - X.α (v, a) (v, a)
      = (∑ b : Fin 4 × Bool, if a ≠ b then (X.α (v, a) (v, b) : ℚ) else 0)
        + ∑ j : SJ X.n, if j.1 ≠ v then (X.α (v, a) j : ℚ) else 0 := by
    intro a
    have h1 : ∑ t : SJ X.n, (X.α (v, a) t : ℚ)
        = ∑ j : SJ X.n, ((if j.1 = v then (X.α (v, a) j : ℚ) else 0)
          + (if j.1 ≠ v then (X.α (v, a) j : ℚ) else 0)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : j.1 = v <;> simp [h]
    have h2 : ∑ j : SJ X.n, (if j.1 = v then (X.α (v, a) j : ℚ) else 0)
        = ∑ b : Fin 4 × Bool, (X.α (v, a) (v, b) : ℚ) := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single v]
      · simp
      · intro u _ hu; simp [hu]
      · intro h; exact absurd (mem_univ v) h
    have h3 : ∑ b : Fin 4 × Bool, (X.α (v, a) (v, b) : ℚ)
        = (∑ b : Fin 4 × Bool, if a ≠ b then (X.α (v, a) (v, b) : ℚ) else 0) + X.α (v, a) (v, a) := by
      rw [← Finset.sum_erase_add _ _ (mem_univ a)]
      congr 1
      rw [← Finset.sum_erase_add _ _ (mem_univ a)]
      simp only [ne_eq, not_true_eq_false, ite_false, add_zero]
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have : b ≠ a := Finset.ne_of_mem_erase hb
      simp [Ne.symm this]
    rw [h1, Finset.sum_add_distrib, h2, h3]; ring
  simp only [hsplit, mul_add, Finset.sum_add_distrib]
  have h2 : (∑ a : Fin 4 × Bool, ∑ j : SJ X.n,
      if j.1 ≠ v then (X.α (v, a) j : ℚ) * eps a.1 a.2 else 0)
      = ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ) * ∑ j : SJ X.n,
        if j.1 ≠ v then (X.α (v, a) j : ℚ) else 0 := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  rw [h2]
  ring

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

theorem J4_symm (u v : Fin X.n) : X.J4 u v = X.J4 v u := by
  unfold J4
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [X.α_symm]; ring

theorem Jc_eq (u v : Fin X.n) : X.Jc u v = (X.J4 u v : ℚ) / 4 := by
  unfold Jc J4; push_cast; ring

/-- block-level tardiness offset -/
def ηB (u v : Fin X.n) : ℤ := if u = v then X.eta u else X.eta (max u v)
theorem etabar_eq (s t : SJ X.n) : X.etabar s t = X.ηB s.1 t.1 := rfl

/-- linear and quadratic parts of the coded objective (8.26) -/
def linC (σ : Fin X.n → Bool) : ℚ := ∑ u, (X.astar u + X.ev u) * sgnQ (σ u)
def quadC (σ : Fin X.n → Bool) : ℚ :=
  ∑ u, ∑ v, if u < v then X.Jc u v * sgnQ (σ u) * sgnQ (σ v) else 0

/-- the σ-independent part of `R₀` on the coded state space -/
def Cexp : ℚ :=
  (1/8) * (∑ s : SJ X.n, ∑ t : SJ X.n, (X.α s t : ℚ)) - (1/4) * (∑ s : SJ X.n, (X.α s s : ℚ))
  + (1/8) * (∑ u, (X.J4 u u : ℚ))
  + (1/2) * (∑ u, ∑ v, (X.ηB u v : ℚ) * X.β u * X.β v)
  + (1/4) * (∑ u, (X.eta u : ℚ) * X.Qsq u)

theorem sum_sgn_diag (σ : Fin X.n → Bool) (F : Fin X.n → Fin X.n → ℚ)
    (hF : ∀ u v, F u v = F v u) :
    ∑ u, ∑ v, sgnQ (σ u) * sgnQ (σ v) * F u v
      = ∑ u, F u u + 2 * ∑ u, ∑ v, if u < v then F u v * sgnQ (σ u) * sgnQ (σ v) else 0 := by
  have hdiag : ∀ u, sgnQ (σ u) * sgnQ (σ u) = 1 := by intro u; cases σ u <;> simp [sgnQ]
  have htri : ∀ u v : Fin X.n, sgnQ (σ u) * sgnQ (σ v) * F u v
      = (if u = v then F u u else 0)
        + (if u < v then F u v * sgnQ (σ u) * sgnQ (σ v) else 0)
        + (if v < u then F u v * sgnQ (σ u) * sgnQ (σ v) else 0) := by
    intro u v
    rcases lt_trichotomy u v with h | h | h
    · simp [h, ne_of_lt h, not_lt.mpr h.le]; ring
    · subst h; simp [hdiag]
    · simp [h, ne_of_gt h, not_lt.mpr h.le]; ring
  simp only [htri, Finset.sum_add_distrib]
  have h1 : ∑ u : Fin X.n, ∑ v : Fin X.n, (if u = v then F u u else 0) = ∑ u, F u u := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  have h2 : (∑ u : Fin X.n, ∑ v : Fin X.n, if v < u then F u v * sgnQ (σ u) * sgnQ (σ v) else 0)
      = ∑ u : Fin X.n, ∑ v : Fin X.n, if u < v then F u v * sgnQ (σ u) * sgnQ (σ v) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    split_ifs
    · rw [hF]; ring
    · rfl
  rw [h1, h2]; ring

/-- **Coded expansion (8.26).** On coded assignments the residual of the load lock is a
constant plus the target field plus the field error plus the cross-block couplings. -/
theorem R0_coded (_hn : 0 < X.n) (σ : Fin X.n → Bool) :
    X.R0 (X.xE (X.codedE σ)) = X.Cexp + X.linC σ + X.quadC σ := by
  set x := X.xE (X.codedE σ) with hx
  have hxs : ∀ s, x s = (1 + X.spin σ s) / 2 := fun s => X.xE_coded σ s
  have hsq := X.spin_sq σ
  -- P1
  have hS : ∑ s : SJ X.n, ∑ t : SJ X.n, x s * x t * (X.α s t : ℚ)
      = (1/4) * (∑ s : SJ X.n, ∑ t : SJ X.n, (X.α s t : ℚ))
        + (1/4) * (∑ s : SJ X.n, ∑ t : SJ X.n, X.spin σ s * (X.α s t : ℚ))
        + (1/4) * (∑ s : SJ X.n, ∑ t : SJ X.n, X.spin σ t * (X.α s t : ℚ))
        + (1/4) * (∑ s : SJ X.n, ∑ t : SJ X.n, X.spin σ s * X.spin σ t * (X.α s t : ℚ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hxs, hxs]; ring
  have hD : ∑ s : SJ X.n, x s * x s * (X.α s s : ℚ)
      = (1/2) * (∑ s : SJ X.n, (X.α s s : ℚ)) + (1/2) * ∑ s : SJ X.n, X.spin σ s * X.α s s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hxs]
    linear_combination ((X.α s s : ℚ) / 4) * hsq s
  have e3 : ∑ s : SJ X.n, ∑ t : SJ X.n, X.spin σ t * (X.α s t : ℚ)
      = ∑ s : SJ X.n, X.spin σ s * ∑ t : SJ X.n, (X.α s t : ℚ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => by rw [X.α_symm_q])
  have e4 : ∑ s : SJ X.n, ∑ t : SJ X.n, X.spin σ s * (X.α s t : ℚ)
      = ∑ s : SJ X.n, X.spin σ s * ∑ t : SJ X.n, (X.α s t : ℚ) := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
  have hP1 : X.psum (fun s t => x s * x t * X.α s t)
      = (1/8) * ((∑ s : SJ X.n, ∑ t : SJ X.n, (X.α s t : ℚ))
          + 2 * (∑ s : SJ X.n, X.spin σ s * ∑ t : SJ X.n, (X.α s t : ℚ))
          + (∑ s : SJ X.n, ∑ t : SJ X.n, X.spin σ s * X.spin σ t * X.α s t))
        - (1/4) * ((∑ s : SJ X.n, (X.α s s : ℚ)) + ∑ s : SJ X.n, X.spin σ s * X.α s s) := by
    rw [X.psum_eq_half _ (by intro s t; rw [X.α_symm_q]; ring), hS, hD, e3, e4]
    ring
  -- A2 in block form
  have hA2 : ∑ s : SJ X.n, ∑ t : SJ X.n, X.spin σ s * X.spin σ t * (X.α s t : ℚ)
      = ∑ u, ∑ v, sgnQ (σ u) * sgnQ (σ v) * (X.J4 u v : ℚ) := by
    rw [X.sum_pairs_blocks]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    unfold J4; push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    unfold spin; ring
  -- A1 - D1 in block form
  have hA1 : (∑ s : SJ X.n, X.spin σ s * ∑ t : SJ X.n, (X.α s t : ℚ))
      - ∑ s : SJ X.n, X.spin σ s * X.α s s = ∑ u, sgnQ (σ u) * (4 * X.a0 u) := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [X.a0_eq]
    rw [show (4:ℚ) * ((1/4) * ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ)
        * ((∑ t : SJ X.n, (X.α (u, a) t : ℚ)) - X.α (u, a) (u, a)))
        = ∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ)
        * ((∑ t : SJ X.n, (X.α (u, a) t : ℚ)) - X.α (u, a) (u, a)) by ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold spin; ring
  -- P2 + P3
  have hy : ∀ s, 1 - x s = (1 - X.spin σ s) / 2 := by intro s; rw [hxs]; ring
  have hyy : ∀ s, (1 - x s) * (1 - x s) = 1 - x s := by
    intro s; rw [hy]; have := hsq s; nlinarith [this]
  have hP2 : X.psum (fun s t => (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.etabar s t))
      = (1/2) * (∑ u, ∑ v, (X.ηB u v : ℚ) * X.β u * X.β v)
        - (1/2) * ∑ s, (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1) := by
    rw [X.psum_eq_half _ (by intro s t; rw [X.etabar_symm]; ring)]
    congr 1
    · congr 1
      have := X.sum_block2 (fun u v => (X.ηB u v : ℚ)) (fun s => (1 - x s) * X.pS s)
      have e : ∀ s t : SJ X.n, (1 - x s) * (1 - x t) * ((X.pS s : ℚ) * X.pS t * X.etabar s t)
          = (X.ηB s.1 t.1 : ℚ) * ((1 - x s) * X.pS s) * ((1 - x t) * X.pS t) := by
        intro s t; rw [X.etabar_eq]; ring
      simp only [e]
      rw [this]
      refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
      have hu := X.bq_coded σ u
      have hv := X.bq_coded σ v
      unfold bq at hu hv
      rw [hu, hv]
    · congr 1
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [hyy, X.etabar_self]; ring
  have hq : ∀ u, ∑ a : Fin 4 × Bool, (1 - x (u, a)) * (X.pS (u, a) : ℚ) ^ 2
      = (1/2) * X.Qsq u - (1/2) * sgnQ (σ u) * X.Dv u := by
    intro u
    unfold Qsq Dv
    push_cast
    rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hy]; unfold spin; ring
  have hP3 : ∑ s, (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1)
      = (1/2) * (∑ u, (X.eta u : ℚ) * X.Qsq u) - (1/2) * ∑ u, (X.eta u : ℚ) * sgnQ (σ u) * X.Dv u := by
    have := X.sum_block1 (fun u => (X.eta u : ℚ)) (fun s => (1 - x s) * (X.pS s : ℚ) ^ 2)
    rw [show ∑ s, (1 - x s) * ((X.pS s : ℚ) ^ 2 * X.eta s.1)
        = ∑ s : SJ X.n, (X.eta s.1 : ℚ) * ((1 - x s) * (X.pS s : ℚ) ^ 2) from
        Finset.sum_congr rfl (fun s _ => by ring), this]
    simp only [hq]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => by ring)
  -- assemble
  unfold R0
  rw [hP1, hP2, hP3, hA2, X.sum_sgn_diag σ (fun u v => (X.J4 u v : ℚ))
    (by intro u v; rw [X.J4_symm])]
  have hlin : X.linC σ = ∑ u, sgnQ (σ u) * X.a0 u - (1/4) * ∑ u, (X.eta u : ℚ) * sgnQ (σ u) * X.Dv u := by
    unfold linC ev
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => by ring)
  have hquad : X.quadC σ = (1/4) * ∑ u, ∑ v,
      if u < v then (X.J4 u v : ℚ) * sgnQ (σ u) * sgnQ (σ v) else 0 := by
    unfold quadC
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [X.Jc_eq]; split_ifs <;> ring
  have hA1' : (∑ s : SJ X.n, X.spin σ s * ∑ t : SJ X.n, (X.α s t : ℚ))
      = ∑ u, sgnQ (σ u) * (4 * X.a0 u) + ∑ s : SJ X.n, X.spin σ s * X.α s s := by
    rw [← hA1]; ring
  rw [hA1', hlin, hquad]
  unfold Cexp
  have h4 : ∑ u, sgnQ (σ u) * (4 * X.a0 u) = 4 * ∑ u, sgnQ (σ u) * X.a0 u := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun u _ => by ring)
  rw [h4]
  ring

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 11. Reduction I: RXC3 ⟺ RPE (Lemmas I.7–I.9) -/

theorem dpre_zero (v : Fin X.n) : X.dpre v 0 = 0 := by simp [dpre]

theorem dpre_succ (v : Fin X.n) (k : ℕ) :
    (X.dpre v (k + 1) : ℤ) = X.dpre v k + ∑ h : Fin 3, (if (X.S v h : ℕ) = k then 1 else 0) := by
  unfold dpre
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  by_cases h1 : (X.S v h : ℕ) < k
  · simp [h1, show (X.S v h : ℕ) < k + 1 by omega, show (X.S v h : ℕ) ≠ k by omega]
  · by_cases h2 : (X.S v h : ℕ) = k
    · simp [h2]
    · simp [h1, h2, show ¬ (X.S v h : ℕ) < k + 1 by omega]

/-- an element occurs at most once in a set -/
theorem occ_le_one (v : Fin X.n) (k : ℕ) :
    ∑ h : Fin 3, (if (X.S v h : ℕ) = k then (1:ℤ) else 0)
      = if ∃ h, (X.S v h : ℕ) = k then 1 else 0 := by
  by_cases hex : ∃ h, (X.S v h : ℕ) = k
  · obtain ⟨h0, hh0⟩ := hex
    rw [ite_eq_left ⟨h0, hh0⟩, Finset.sum_eq_single h0]
    · simp [hh0]
    · intro b _ hb
      have : (X.S v b : ℕ) ≠ k := by
        intro e
        have : X.S v b = X.S v h0 := Fin.ext (e.trans hh0.symm)
        exact hb (X.S_inj v this)
      simp [this]
    · intro h; exact absurd (mem_univ h0) h
  · rw [ite_eq_right hex]
    push Not at hex
    simp [hex]

/-- regularity: the first `k` elements carry `3k` incidences -/
theorem sum_dpre (k : ℕ) (hk : k ≤ X.n) : ∑ v, (X.dpre v k : ℤ) = 3 * k := by
  induction k with
  | zero => simp [dpre_zero]
  | succ k ih =>
    have ih' := ih (by omega)
    simp only [dpre_succ, Finset.sum_add_distrib, ih']
    have hc := X.reg ⟨k, by omega⟩
    have : ∑ v : Fin X.n, ∑ h : Fin 3, (if (X.S v h : ℕ) = k then (1:ℤ) else 0) = 3 := by
      rw [← Fintype.sum_prod_type (f := fun q : Fin X.n × Fin 3 =>
        if (X.S q.1 q.2 : ℕ) = k then (1:ℤ) else 0)]
      rw [Finset.sum_boole]
      have e : (univ.filter (fun q : Fin X.n × Fin 3 => X.S q.1 q.2 = ⟨k, by omega⟩)).card
          = (univ.filter (fun q : Fin X.n × Fin 3 => (X.S q.1 q.2 : ℕ) = k)).card := by
        congr 1
      rw [← e, hc]; norm_num
    rw [this]; push_cast; ring

theorem Cpre_zero (x : Fin X.n → Bool) : X.Cpre x 0 = 0 := by simp [Cpre, dpre_zero]

/-- **Lemma I.7 (prefix-difference identity).** -/
theorem Cpre_succ (x : Fin X.n → Bool) (k : ℕ) :
    X.Cpre x (k + 1) - X.Cpre x k
      = (univ.filter (fun v => x v = true ∧ ∃ h, (X.S v h : ℕ) = k)).card := by
  unfold Cpre
  rw [← Finset.sum_sub_distrib, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [dpre_succ, occ_le_one]
  by_cases hx : x v = true <;> by_cases he : ∃ h, (X.S v h : ℕ) = k <;> simp [hx, he]

/-- **Lemmas I.8 and I.9.** An exact cover is exactly a solution of the prefix equations. -/
theorem exactCover_iff_RPE (x : Fin X.n → Bool) : X.IsExactCover x ↔ X.RPE x := by
  have hcount : ∀ k : Fin X.n,
      (univ.filter (fun v => x v = true ∧ ∃ h, X.S v h = k)).card
        = (univ.filter (fun v => x v = true ∧ ∃ h, (X.S v h : ℕ) = k)).card := by
    intro k; congr 1
  constructor
  · intro hc k hk1 hkn
    induction k with
    | zero => omega
    | succ k ih =>
      have h1 := X.Cpre_succ x k
      have h2 := hc ⟨k, by omega⟩
      rw [hcount] at h2
      simp only at h2
      rw [h2] at h1
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [Cpre_zero] at h1; push_cast at h1 ⊢; linarith
      · have := ih hk (by omega); push_cast at h1 this ⊢; linarith
  · intro hr k
    have h1 := X.Cpre_succ x k
    have hk1 : X.Cpre x (k + 1) = (k : ℤ) + 1 := by
      have := hr (k + 1) (by omega) (by omega); push_cast at this; exact this
    have hk0 : X.Cpre x k = k := by
      rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
      · rw [h, Cpre_zero]; simp
      · exact hr k h k.isLt.le
    rw [hcount]
    have : ((univ.filter (fun v => x v = true ∧ ∃ h, (X.S v h : ℕ) = k)).card : ℤ) = 1 := by
      rw [← h1, hk1, hk0]; ring
    exact_mod_cast this

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ## 12. Master identity (Lemma I.16), residual bound and decision gap -/

/-- main-gap coupling (8.27) -/
def Jmain (u v : Fin X.n) : ℚ := (1/4) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * X.dpre u k * X.dpre v k

/-- prefix penalty `𝒫(x)` (8.28) -/
def Pen (x : Fin X.n → Bool) : ℚ := ∑ k ∈ Icc 1 X.n, ((X.Δ k : ℚ) / 2) * (X.Cpre x k - k) ^ 2

/-- residual `R(σ)` (8.30) -/
def Res (σ : Fin X.n → Bool) : ℚ := ∑ v, X.ev v * sgnQ (σ v)
  + ∑ u, ∑ v, if u < v then (X.Jc u v - X.Jmain u v) * sgnQ (σ u) * sgnQ (σ v) else 0

theorem coded_objective (hn : 0 < X.n) (σ : Fin X.n → Bool) :
    (X.inst.Φ (X.codedE σ) : ℚ) = X.C0 + X.linC σ + X.quadC σ := by
  have hgen : ∀ τ : Fin X.n → Bool,
      (X.inst.Φ (X.codedE τ) : ℚ) = X.K0 + X.Cexp + X.linC τ + X.quadC τ := by
    intro τ
    rw [X.Φ_eq_phiQ X.agrees_inst (X.mem_codedE_anchor τ), X.phiQ_decomp hn _ (X.xE_01 _),
      X.R0_coded hn τ]
    have : X.lockQ (X.xE (X.codedE τ)) = 0 := by unfold lockQ; simp [bq_coded]
    rw [this]; ring
  have hC : (X.Cstar : ℚ) = X.K0 + X.Cexp + X.linC (fun _ => true) + X.quadC (fun _ => true) := by
    unfold Cstar
    rw [X.Φ_pre_eq_inst (X.mem_codedE_anchor _)]
    exact hgen _
  have hl : X.linC (fun _ => true) = ∑ v, (X.astar v + X.ev v) := by
    unfold linC; simp [sgnQ]
  have hq : X.quadC (fun _ => true) = ∑ u, ∑ v, if u < v then X.Jc u v else 0 := by
    unfold quadC; simp [sgnQ]
  have hC0 : X.C0 = X.K0 + X.Cexp := by
    unfold C0; rw [hC, hl, hq]; ring
  rw [hgen, hC0]

theorem sgnQ_eq (b : Bool) : sgnQ b = 2 * (if b then 1 else 0) - 1 := by
  cases b <;> simp [sgnQ]
  norm_num

/-- **Lemma I.16 (exact master decomposition).** -/
theorem master (hn : 0 < X.n) (σ : Fin X.n → Bool) :
    (X.inst.Φ (X.codedE σ) : ℚ) = X.Aconst + X.Pen σ + X.Res σ := by
  rw [X.coded_objective hn σ]
  -- Y_k
  set Y : ℕ → ℚ := fun k => ∑ v, (X.dpre v k : ℚ) * sgnQ (σ v) with hY
  have hYk : ∀ k ∈ Icc 1 X.n, Y k + k = 2 * (X.Cpre σ k - k) := by
    intro k hk
    have hkn : k ≤ X.n := (Finset.mem_Icc.mp hk).2
    have h3 : ∑ v, (X.dpre v k : ℚ) = 3 * k := by
      have := X.sum_dpre k hkn; exact_mod_cast this
    simp only [hY, sgnQ_eq]
    unfold Cpre
    push_cast
    have : ∑ v, (X.dpre v k : ℚ) * (2 * (if σ v = true then (1:ℚ) else 0) - 1)
        = 2 * ∑ v, (X.dpre v k : ℚ) * (if σ v = true then (1:ℚ) else 0) - ∑ v, (X.dpre v k : ℚ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun v _ => by ring)
    rw [this, h3]; ring
  -- the linear target-field part
  have hlin : ∑ v, X.astar v * sgnQ (σ v) = (1/4) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * k * Y k := by
    unfold astar
    simp only [hY, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun v _ => by ring))
  -- the main-gap quadratic part
  have hquad : (∑ u, ∑ v, if u < v then X.Jmain u v * sgnQ (σ u) * sgnQ (σ v) else 0)
      = (1/8) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * (Y k ^ 2 - ∑ v, (X.dpre v k : ℚ) ^ 2) := by
    have hk : ∀ k, (∑ u, ∑ v, if u < v then (X.dpre u k : ℚ) * X.dpre v k * sgnQ (σ u) * sgnQ (σ v) else 0)
        = (1/2) * (Y k ^ 2 - ∑ v, (X.dpre v k : ℚ) ^ 2) := by
      intro k
      have := X.sum_sgn_diag σ (fun u v => (X.dpre u k : ℚ) * X.dpre v k) (by intro u v; ring)
      have hY2 : Y k ^ 2 = ∑ u, ∑ v, sgnQ (σ u) * sgnQ (σ v) * ((X.dpre u k : ℚ) * X.dpre v k) := by
        simp only [hY, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => by ring))
      rw [hY2, this]
      simp only [sq]
      ring
    unfold Jmain
    have e : ∀ u v : Fin X.n, (if u < v then (1/4) * (∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * X.dpre u k * X.dpre v k)
        * sgnQ (σ u) * sgnQ (σ v) else 0)
        = (1/4) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * (if u < v then (X.dpre u k : ℚ) * X.dpre v k
          * sgnQ (σ u) * sgnQ (σ v) else 0) := by
      intro u v
      split_ifs
      · rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      · simp
    simp only [e, ← Finset.mul_sum]
    have swap : ∀ F : Fin X.n → Fin X.n → ℕ → ℚ,
        ∑ u, ∑ v, ∑ k ∈ Icc 1 X.n, F u v k = ∑ k ∈ Icc 1 X.n, ∑ u, ∑ v, F u v k := by
      intro F
      calc ∑ u, ∑ v, ∑ k ∈ Icc 1 X.n, F u v k = ∑ u, ∑ k ∈ Icc 1 X.n, ∑ v, F u v k :=
            Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
        _ = ∑ k ∈ Icc 1 X.n, ∑ u, ∑ v, F u v k := Finset.sum_comm
    rw [swap (fun u v k => (X.Δ k : ℚ) * (if u < v then (X.dpre u k : ℚ) * X.dpre v k
          * sgnQ (σ u) * sgnQ (σ v) else 0))]
    have e2 : ∀ k, (∑ u, ∑ v, (X.Δ k : ℚ) * (if u < v then (X.dpre u k : ℚ) * X.dpre v k
          * sgnQ (σ u) * sgnQ (σ v) else 0))
        = (X.Δ k : ℚ) * ((1/2) * (Y k ^ 2 - ∑ v, (X.dpre v k : ℚ) ^ 2)) := by
      intro k; rw [← hk k, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => by rw [Finset.mul_sum])
    simp only [e2]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  -- assemble
  unfold linC quadC Res Pen Aconst
  have hsplit_lin : ∑ u, (X.astar u + X.ev u) * sgnQ (σ u)
      = ∑ u, X.astar u * sgnQ (σ u) + ∑ v, X.ev v * sgnQ (σ v) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun u _ => by ring)
  have hsplit_quad : (∑ u, ∑ v, if u < v then X.Jc u v * sgnQ (σ u) * sgnQ (σ v) else 0)
      = (∑ u, ∑ v, if u < v then X.Jmain u v * sgnQ (σ u) * sgnQ (σ v) else 0)
        + ∑ u, ∑ v, if u < v then (X.Jc u v - X.Jmain u v) * sgnQ (σ u) * sgnQ (σ v) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs <;> ring
  rw [hsplit_lin, hsplit_quad, hlin, hquad]
  have hpen : ∑ k ∈ Icc 1 X.n, ((X.Δ k : ℚ) / 2) * (X.Cpre σ k - k) ^ 2
      = ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) / 8 * (Y k + k) ^ 2 := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hYk k hk]; ring
  rw [hpen]
  have hfin : (1/4) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * k * Y k
      + (1/8) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * (Y k ^ 2 - ∑ v, (X.dpre v k : ℚ) ^ 2)
      = ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) / 8 * (Y k + k) ^ 2
        - (1/8) * ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * ((k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  linear_combination hfin

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ### field correction (8.16)–(8.19) -/

theorem Dv_eq' (v : Fin X.n) :
    X.Dv v = 2 * X.M * ((X.ht v 1 : ℤ) + X.ht v 2 + X.ht v 3) + 22134 := by
  rw [Dv_eq, Fin.sum_univ_four]
  simp [mass, cA, P, ht_zero, Qc]
  ring

theorem Dv_pos (v : Fin X.n) : 0 < X.Dv v := by
  rw [Dv_eq']
  have := X.M_pos
  have : (0:ℤ) ≤ (X.ht v 1 : ℤ) + X.ht v 2 + X.ht v 3 := by positivity
  nlinarith

theorem Dv_le (v : Fin X.n) : X.Dv v ≤ 6 * X.n * X.M + 22134 := by
  rw [Dv_eq']
  have h1 : (X.ht v 1 : ℤ) ≤ X.n := by exact_mod_cast X.ht_le v 1
  have h2 : (X.ht v 2 : ℤ) ≤ X.n := by exact_mod_cast X.ht_le v 2
  have h3 : (X.ht v 3 : ℤ) ≤ X.n := by exact_mod_cast X.ht_le v 3
  have := X.M_pos
  nlinarith

/-- `|e_v| ≤ D_v / 8` (8.19) -/
theorem abs_ev_le (v : Fin X.n) : |X.ev v| ≤ (X.Dv v : ℚ) / 8 := by
  have hD : (0:ℚ) < X.Dv v := by exact_mod_cast X.Dv_pos v
  set z : ℚ := (4 * (X.a0 v - X.astar v)) / (X.Dv v : ℚ) with hz
  have hr := abs_sub_round z
  have heta : (X.eta v : ℚ) = round z := by unfold eta; rw [← hz]
  have hev : X.ev v = ((X.Dv v : ℚ) / 4) * (z - round z) := by
    unfold ev; rw [heta, hz]; field_simp; ring
  rw [hev, abs_mul, abs_of_pos (by positivity : (0:ℚ) < (X.Dv v : ℚ) / 4)]
  calc (X.Dv v : ℚ) / 4 * |z - round z| ≤ (X.Dv v : ℚ) / 4 * (1/2) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (X.Dv v : ℚ) / 8 := by ring

/-! ### within-band residual of the couplings -/

theorem gapsum_reindex (u v : Fin X.n) :
    ∑ η ∈ range X.n, X.gap η * X.dpre u (X.n - η) * X.dpre v (X.n - η)
      = ∑ k ∈ Icc 1 X.n, X.Δ k * X.dpre u k * X.dpre v k := by
  refine Finset.sum_nbij' (fun η => X.n - η) (fun k => X.n - k) ?_ ?_ ?_ ?_ ?_
  · intro η hη; simp only [Finset.mem_range, Finset.mem_Icc] at hη ⊢; omega
  · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
  · intro η hη; simp only [Finset.mem_range] at hη; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro η hη
    simp only [Finset.mem_range] at hη
    unfold Δ
    rw [show X.n - (X.n - η) = η by omega]

theorem Jc_sub_Jmain (hn : 0 < X.n) {u v : Fin X.n} (huv : u ≠ v) :
    0 ≤ X.Jc u v - X.Jmain u v ∧ X.Jc u v - X.Jmain u v ≤ (9/4) * X.W := by
  have hd := X.J4_decomp hn huv
  rw [X.gapsum_reindex] at hd
  have hJ : X.Jc u v - X.Jmain u v = (1/4) * ∑ η ∈ range (X.n + 1), (X.bandSum η u v : ℚ) := by
    rw [X.Jc_eq, hd]; unfold Jmain; push_cast; ring
  rw [hJ]
  have hb : ∀ η ∈ range (X.n + 1), (0:ℚ) ≤ X.bandSum η u v ∧
      (X.bandSum η u v : ℚ) ≤ 9 * ((X.hi η : ℚ) - X.lo η) := by
    intro η hη
    have := bandSum_bounds hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hη)) u v
    constructor
    · exact_mod_cast this.1
    · have := this.2; exact_mod_cast this
  constructor
  · have := Finset.sum_nonneg (fun η hη => (hb η hη).1); linarith
  · have h1 := Finset.sum_le_sum (fun η hη => (hb η hη).2)
    have hW : (X.W : ℚ) = ∑ η ∈ range (X.n + 1), ((X.hi η : ℚ) - X.lo η) := by
      unfold W; push_cast; rfl
    rw [hW]
    rw [← Finset.mul_sum] at h1
    linarith

theorem W_nonneg (hn : 0 < X.n) : 0 ≤ X.W :=
  Finset.sum_nonneg (fun η hη => by
    have := lo_le_hi hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hη)); linarith)

theorem count_lt : (∑ u : Fin X.n, ∑ v : Fin X.n, if u < v then (1:ℚ) else 0)
    ≤ (X.n : ℚ) ^ 2 / 2 := by
  have h1 : (∑ u : Fin X.n, ∑ v : Fin X.n, if v < u then (1:ℚ) else 0)
      = ∑ u : Fin X.n, ∑ v : Fin X.n, if u < v then (1:ℚ) else 0 := by
    rw [Finset.sum_comm]
  have h2 : (∑ u : Fin X.n, ∑ v : Fin X.n, (1:ℚ))
      = (∑ u : Fin X.n, ∑ v : Fin X.n, if u < v then (1:ℚ) else 0)
        + (∑ u : Fin X.n, ∑ v : Fin X.n, if v < u then (1:ℚ) else 0)
        + ∑ u : Fin X.n, ∑ v : Fin X.n, if u = v then (1:ℚ) else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rcases lt_trichotomy u v with h | h | h
    · simp [h, ne_of_lt h, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, ne_of_gt h, not_lt.mpr h.le]
  have h3 : (∑ u : Fin X.n, ∑ v : Fin X.n, (1:ℚ)) = (X.n : ℚ) ^ 2 := by simp; ring
  have h4 : 0 ≤ ∑ u : Fin X.n, ∑ v : Fin X.n, if u = v then (1:ℚ) else 0 :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num))
  rw [h1] at h2
  linarith

/-- **Residual bound (8.32)**: `|R(σ)| ≤ Γ`. -/
theorem abs_Res_le (hn : 0 < X.n) (σ : Fin X.n → Bool) : |X.Res σ| ≤ X.Gam := by
  unfold Res Gam
  have hs : ∀ b : Bool, |sgnQ b| = 1 := by intro b; cases b <;> simp [sgnQ]
  have h1 : |∑ v, X.ev v * sgnQ (σ v)| ≤ (1/8) * ∑ v, (X.Dv v : ℚ) := by
    calc |∑ v, X.ev v * sgnQ (σ v)| ≤ ∑ v, |X.ev v * sgnQ (σ v)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ v, |X.ev v| := Finset.sum_congr rfl (fun v _ => by rw [abs_mul, hs, mul_one])
      _ ≤ ∑ v, (X.Dv v : ℚ) / 8 := Finset.sum_le_sum (fun v _ => X.abs_ev_le v)
      _ = (1/8) * ∑ v, (X.Dv v : ℚ) := by rw [Finset.mul_sum]; ring_nf
  have hW := X.W_nonneg hn
  have hW' : (0:ℚ) ≤ X.W := by exact_mod_cast hW
  have h2 : |∑ u, ∑ v, if u < v then (X.Jc u v - X.Jmain u v) * sgnQ (σ u) * sgnQ (σ v) else 0|
      ≤ (9/8) * (X.n : ℚ) ^ 2 * X.W := by
    calc _ ≤ ∑ u, |∑ v, if u < v then (X.Jc u v - X.Jmain u v) * sgnQ (σ u) * sgnQ (σ v) else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u, ∑ v, |if u < v then (X.Jc u v - X.Jmain u v) * sgnQ (σ u) * sgnQ (σ v) else 0| :=
          Finset.sum_le_sum (fun u _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ u : Fin X.n, ∑ v : Fin X.n, if u < v then (9/4) * (X.W : ℚ) else 0 := by
          refine Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => ?_))
          split_ifs with h
          · rw [abs_mul, abs_mul, hs, hs, mul_one, mul_one]
            have := X.Jc_sub_Jmain hn (ne_of_lt h)
            rw [abs_of_nonneg this.1]; exact this.2
          · simp
      _ = (9/4) * (X.W : ℚ) * ∑ u : Fin X.n, ∑ v : Fin X.n, if u < v then (1:ℚ) else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun v _ => by split_ifs <;> simp)
      _ ≤ (9/4) * (X.W : ℚ) * ((X.n : ℚ) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left X.count_lt (by positivity)
      _ = (9/8) * (X.n : ℚ) ^ 2 * X.W := by ring
  have := abs_add_le (∑ v, X.ev v * sgnQ (σ v))
    (∑ u, ∑ v, if u < v then (X.Jc u v - X.Jmain u v) * sgnQ (σ u) * sgnQ (σ v) else 0)
  linarith

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-! ### the decision gap (8.33) -/

section
variable {X}
variable (hn : 0 < X.n)
include hn

theorem Wb_le : X.Wb ≤ 15 * X.NN ^ 52 := by
  unfold Wb
  have hnN := n_lt_NN hn
  have hn0 : (0:ℤ) ≤ X.n := by positivity
  have hn2 : (X.n : ℤ) ^ 2 ≤ X.NN ^ 2 := pow_le_pow_left₀ hn0 hnN.le 2
  rw [G_eq, M_eq, T_eq]
  have p50 := pow_pos' hn 50
  have p40 := pow_pos' hn 40
  have t1 : 10 * (X.n : ℤ) ^ 2 * X.NN ^ 50 ≤ 10 * X.NN ^ 52 := by
    have := mul_le_mul_of_nonneg_right hn2 p50.le
    rw [show X.NN ^ 52 = X.NN ^ 2 * X.NN ^ 50 by ring]; linarith
  have t2 : 2 * (X.n : ℤ) * X.NN ^ 50 ≤ 2 * X.NN ^ 52 := by
    have := mul_le_mul_of_nonneg_right hnN.le p50.le
    have h51 : X.NN * X.NN ^ 50 ≤ X.NN ^ 52 := by
      rw [show X.NN * X.NN ^ 50 = X.NN ^ 51 by ring]; exact pow_mono hn (by norm_num)
    linarith
  have t3 : 2 * (X.n : ℤ) ^ 2 * X.NN ^ 40 ≤ 2 * X.NN ^ 52 := by
    have := mul_le_mul_of_nonneg_right hn2 p40.le
    have h42 : X.NN ^ 2 * X.NN ^ 40 ≤ X.NN ^ 52 := by
      rw [show X.NN ^ 2 * X.NN ^ 40 = X.NN ^ 42 by ring]; exact pow_mono hn (by norm_num)
    linarith
  have t4 : 20003 * (X.NN ^ 20 + X.n) ≤ X.NN ^ 52 := by
    have a1 : X.NN ^ 20 ≤ X.NN ^ 30 := pow_mono hn (by norm_num)
    have a2 : (X.n : ℤ) ≤ X.NN ^ 30 := by
      have : X.NN ^ 1 ≤ X.NN ^ 30 := pow_mono hn (by norm_num)
      simp at this; linarith
    have a3 : 65536 * X.NN ^ 30 ≤ X.NN ^ 38 := by
      have := mul_pow_le hn 65536 30 8 (by norm_num); simpa using this
    have a4 : X.NN ^ 38 ≤ X.NN ^ 52 := pow_mono hn (by norm_num)
    have := pow_pos' hn 30
    linarith
  linarith

theorem W_le : X.W ≤ 15 * X.NN ^ 53 := by
  unfold W
  have h : ∀ η ∈ range (X.n + 1), X.hi η - X.lo η ≤ 15 * X.NN ^ 52 := by
    intro η hη
    exact le_trans (width_le hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hη))) (Wb_le hn)
  have := Finset.sum_le_sum h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hN : ((X.n + 1 : ℕ) : ℤ) = X.NN := by unfold NN; push_cast; ring
  rw [hN] at this
  rw [show X.NN ^ 53 = X.NN * X.NN ^ 52 by ring]
  linarith

theorem sumDv_le : ∑ v, X.Dv v ≤ X.NN ^ 55 := by
  have h : ∀ v ∈ (univ : Finset (Fin X.n)), X.Dv v ≤ 6 * X.n * X.M + 22134 :=
    fun v _ => X.Dv_le v
  have := Finset.sum_le_sum h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hnN := n_lt_NN hn
  have hn0 : (0:ℤ) ≤ X.n := by positivity
  rw [M_eq] at this
  have p40 := pow_pos' hn 40
  have e1 : (X.n : ℤ) * (6 * X.n * X.NN ^ 40 + 22134) ≤ X.NN * (6 * X.NN * X.NN ^ 40 + 22134) := by
    have : 6 * (X.n : ℤ) * X.NN ^ 40 ≤ 6 * X.NN * X.NN ^ 40 := by nlinarith
    nlinarith
  have e2 : X.NN * (6 * X.NN * X.NN ^ 40 + 22134) = 6 * X.NN ^ 42 + 22134 * X.NN := by ring
  have e3 : 6 * X.NN ^ 42 + 22134 * X.NN ≤ X.NN ^ 55 := by
    have a1 : X.NN ^ 1 ≤ X.NN ^ 42 := pow_mono hn (by norm_num)
    have a2 : 65536 * X.NN ^ 42 ≤ X.NN ^ 50 := by
      have := mul_pow_le hn 65536 42 8 (by norm_num); simpa using this
    have a3 : X.NN ^ 50 ≤ X.NN ^ 55 := pow_mono hn (by norm_num)
    simp at a1
    have := pow_pos' hn 42
    linarith
  linarith

/-- `4 Γ < G M`, hence `Δ_min / 2 > 2 Γ` -/
theorem four_Gam_lt : 4 * X.Gam < (X.G : ℚ) * X.M := by
  have hW := W_le hn
  have hD := sumDv_le hn
  have hW0 := X.W_nonneg hn
  have hnN := n_lt_NN hn
  have hn0 : (0:ℤ) ≤ X.n := by positivity
  have hn2 : (X.n : ℤ) ^ 2 ≤ X.NN ^ 2 := pow_le_pow_left₀ hn0 hnN.le 2
  have hnW : (X.n : ℤ) ^ 2 * X.W ≤ 15 * X.NN ^ 55 := by
    have := mul_le_mul hn2 hW hW0 (by positivity)
    rw [show X.NN ^ 55 = X.NN ^ 2 * X.NN ^ 53 by ring]; linarith
  have hGM : X.G * X.M = X.NN ^ 60 := by rw [G_eq, M_eq]; ring
  have h60 : 1024 * X.NN ^ 55 ≤ X.NN ^ 60 := by
    have := mul_pow_le hn 1024 55 5 (by norm_num); simpa using this
  have p55 := pow_pos' hn 55
  -- an integer inequality, then cast
  have hint : 36 * ((X.n : ℤ) ^ 2 * X.W) + 4 * ∑ v, X.Dv v < 8 * (X.G * X.M) := by
    rw [hGM]; linarith
  have hcast : ((36 * ((X.n : ℤ) ^ 2 * X.W) + 4 * ∑ v, X.Dv v : ℤ) : ℚ)
      < ((8 * (X.G * X.M) : ℤ) : ℚ) := Int.cast_lt.mpr hint
  push_cast at hcast
  unfold Gam
  linarith

theorem Δ_gt {k : ℕ} (hk : k ∈ Icc 1 X.n) : X.G * X.M < X.Δ k := by
  unfold Δ
  have := Finset.mem_Icc.mp hk
  exact gap_gt hn (by omega)

theorem Pen_nonneg (x : Fin X.n → Bool) : 0 ≤ X.Pen x :=
  Finset.sum_nonneg (fun k hk => by
    have : (0:ℚ) < X.Δ k := by
      have := Δ_gt hn hk; have := mul_pos X.G_pos X.M_pos; exact_mod_cast (by linarith)
    positivity)

theorem Pen_ge {x : Fin X.n → Bool} {k : ℕ} (hk : k ∈ Icc 1 X.n) (hne : X.Cpre x k ≠ k) :
    (X.Δ k : ℚ) / 2 ≤ X.Pen x := by
  have hpos : ∀ k ∈ Icc 1 X.n, (0:ℚ) ≤ ((X.Δ k : ℚ) / 2) * (X.Cpre x k - k) ^ 2 := by
    intro k hk
    have : (0:ℚ) < X.Δ k := by
      have := Δ_gt hn hk; have := mul_pos X.G_pos X.M_pos; exact_mod_cast (by linarith)
    positivity
  have := Finset.single_le_sum hpos hk
  have hsq : (1:ℚ) ≤ ((X.Cpre x k : ℚ) - k) ^ 2 := by
    have h1 : X.Cpre x k - (k : ℤ) ≠ 0 := sub_ne_zero.mpr hne
    have h2 := Int.one_le_abs h1
    have h3 : (1:ℤ) ≤ (X.Cpre x k - (k : ℤ)) ^ 2 := by nlinarith [sq_abs (X.Cpre x k - (k : ℤ))]
    exact_mod_cast h3
  have hΔ : (0:ℚ) < X.Δ k := by
    have := Δ_gt hn hk; have := mul_pos X.G_pos X.M_pos; exact_mod_cast (by linarith)
  unfold Pen
  nlinarith

end

/-! ## 13. Main theorem -/

/-- the early set of the minimiser carries a coded structure -/
theorem coded_of_balanced (hn : 0 < X.n) {E : Finset (Job X.n)} (hE : Job.anchor ∈ E)
    (hb : ∀ u, X.bq (X.xE E) u = X.β u) : ∃ σ : Fin X.n → Bool, E = X.codedE σ := by
  have hblock : ∀ u, ∃ s : Bool, ∀ a : Fin 4 × Bool,
      decide (Job.st (u, a) ∈ E) = decide (sgn s * eps a.1 a.2 = 1) := by
    intro u
    apply X.two_states hn u (fun a => decide (Job.st (u, a) ∈ E))
    have := hb u
    unfold bq xE at this
    have h : ((∑ a : Fin 4 × Bool, (if decide (Job.st (u, a) ∈ E) = true then 0 else X.pS (u, a)) : ℤ) : ℚ)
        = X.β u := by
      rw [← this]; push_cast
      refine Finset.sum_congr rfl (fun a _ => ?_)
      by_cases h : Job.st (u, a) ∈ E <;> simp [h]
    exact_mod_cast h
  choose σ hσ using hblock
  refine ⟨σ, ?_⟩
  ext j
  rcases Job.cases j with rfl | ⟨s, rfl⟩
  · simp [hE, X.mem_codedE_anchor]
  · rw [X.mem_codedE_st]
    have := hσ s.1 s.2
    simp only [decide_eq_decide] at this
    exact this

/-- **Theorem I.2 (correctness of the reduction).** For every RXC3 instance with `n ≥ 1`
(hence `n ≥ 3`), the instance has an exact cover iff the constructed AWET instance has a
schedule of cost at most `B`. -/
theorem reduction_correct (hn : 0 < X.n) : X.HasExactCover ↔ X.inst.Yes X.Bnd := by
  rw [Inst.yes_iff]
  constructor
  · -- Lemma I.17
    rintro ⟨x, hx⟩
    refine ⟨X.codedE x, ?_⟩
    have hrpe := (X.exactCover_iff_RPE x).mp hx
    have hpen : X.Pen x = 0 := by
      unfold Pen
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have := Finset.mem_Icc.mp hk
      rw [hrpe k this.1 this.2]; push_cast; ring
    have hm := X.master hn x
    have hr := abs_le.mp (X.abs_Res_le hn x)
    have hle : (X.inst.Φ (X.codedE x) : ℚ) ≤ X.Aconst + X.Gam := by
      rw [hm, hpen]; linarith [hr.2]
    unfold Bnd
    exact Int.le_floor.mpr hle
  · -- Lemma I.18
    rintro ⟨E, hE⟩
    obtain ⟨E0, -, hmin⟩ := Finset.exists_min_image (univ : Finset (Finset (Job X.n)))
      X.inst.Φ ⟨E, mem_univ E⟩
    have hmin' : ∀ F, X.inst.Φ E0 ≤ X.inst.Φ F := fun F => hmin F (mem_univ F)
    have hE0 : X.inst.Φ E0 ≤ X.Bnd := le_trans (hmin' E) hE
    -- Gate 1: the anchor is early
    have hanc : Job.anchor ∈ E0 := by
      by_contra h
      have h1 := X.anchor_gate h
      have h2 : X.Cstar = X.inst.Φ (X.codedE (fun _ => true)) :=
        X.Φ_pre_eq_inst (X.mem_codedE_anchor _)
      have := hmin' (X.codedE (fun _ => true))
      omega
    -- Gate 2: every block is coded
    have hbal : ∀ u, X.bq (X.xE E0) u = X.β u := by
      by_contra h
      push Not at h
      have := X.load_lock hn hanc h
      have := hmin' (X.codedE (fun _ => true))
      omega
    obtain ⟨σ, rfl⟩ := X.coded_of_balanced hn hanc hbal
    -- Gate 3: every prefix equation is exact
    refine ⟨σ, (X.exactCover_iff_RPE σ).mpr ?_⟩
    intro k hk1 hkn
    by_contra hne
    have hk : k ∈ Icc 1 X.n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
    have hm := X.master hn σ
    have hr := abs_le.mp (X.abs_Res_le hn σ)
    have hB : (X.Bnd : ℚ) ≤ X.Aconst + X.Gam := Int.floor_le _
    have hΦ : ((X.inst.Φ (X.codedE σ) : ℤ) : ℚ) ≤ X.Bnd := by exact_mod_cast hE0
    have hP := Pen_ge hn hk hne
    have hΔ : ((X.G : ℚ) * X.M) < X.Δ k := by exact_mod_cast Δ_gt hn hk
    have h4 := four_Gam_lt hn
    linarith [hr.1]

end RXC3
end AWET

namespace AWET
namespace RXC3
variable (X : RXC3)

/-- the degenerate empty instance (`n = 0`) is a yes-instance on both sides -/
theorem reduction_correct_zero (hn : X.n = 0) : X.HasExactCover ↔ X.inst.Yes X.Bnd := by
  have hcov : X.HasExactCover := ⟨fun _ => true, fun k => absurd k.isLt (by omega)⟩
  have hyes : X.inst.Yes X.Bnd := by
    rw [Inst.yes_iff]
    refine ⟨X.codedE (fun _ => true), ?_⟩
    have h1 : X.inst.Φ (X.codedE (fun _ => true)) = X.Cstar :=
      (X.Φ_pre_eq_inst (X.mem_codedE_anchor _)).symm
    have hA : X.Aconst + X.Gam = X.Cstar := by
      have e1 : (univ : Finset (Fin X.n)) = ∅ := by
        rw [Finset.univ_eq_empty_iff]; rw [hn]; exact Fin.isEmpty'
      have e2 : Icc 1 X.n = ∅ := by rw [hn]; rfl
      unfold Aconst Gam C0
      rw [e1, e2]; simp [hn]
    unfold Bnd; rw [hA, h1]; simp
  exact ⟨fun _ => hyes, fun _ => hcov⟩

/-- **Correctness of the strong reduction RXC3 → AWET (Theorem I.2, Lemmas I.17–I.18).** -/
theorem reduction_iff : X.HasExactCover ↔ X.inst.Yes X.Bnd := by
  rcases Nat.eq_zero_or_pos X.n with h | h
  · exact X.reduction_correct_zero h
  · exact X.reduction_correct h

end RXC3
end AWET


open Finset

namespace AWET
namespace RXC3
variable {X : RXC3}

/-! ## 14. Polynomial size bounds (Lemma I.19) -/

section size
variable (hn : 0 < X.n)
include hn

/-! ### generic power arithmetic with `N = n + 1 ≥ 4` -/

theorem Npos : (0:ℤ) < X.NN := by linarith [NN_ge_four hn]

theorem pw_mono {a b : ℕ} (h : a ≤ b) : X.NN ^ a ≤ X.NN ^ b := pow_mono hn h

theorem pw_nonneg (a : ℕ) : (0:ℤ) ≤ X.NN ^ a := (pow_pos' hn a).le

/-- `a ≤ N^e₁`, `b ≤ N^e₂` (nonnegative) give `a b ≤ N^e` for `e₁ + e₂ ≤ e` -/
theorem mul_le_pw {a b : ℤ} {e1 e2 : ℕ} (e : ℕ) (he : e1 + e2 ≤ e) (_ha : 0 ≤ a)
    (ha' : a ≤ X.NN ^ e1) (hb : 0 ≤ b) (hb' : b ≤ X.NN ^ e2) : a * b ≤ X.NN ^ e := by
  have h1 : a * b ≤ X.NN ^ e1 * X.NN ^ e2 := mul_le_mul ha' hb' hb (pw_nonneg hn e1)
  rw [← pow_add] at h1
  exact le_trans h1 (pw_mono hn he)

/-- `a, b ≤ N^e₀` give `a + b ≤ N^e` for `e₀ < e` -/
theorem add_le_pw {a b : ℤ} {e0 : ℕ} (e : ℕ) (he : e0 < e) (ha : a ≤ X.NN ^ e0)
    (hb : b ≤ X.NN ^ e0) : a + b ≤ X.NN ^ e := by
  have h2 := mul_pow_le hn 2 e0 1 (by norm_num)
  have h3 : X.NN ^ (e0 + 1) ≤ X.NN ^ e := pw_mono hn (by omega)
  linarith

theorem const_le_pw (c : ℤ) (k e : ℕ) (hc : c ≤ 4 ^ k) (hke : k ≤ e) : c ≤ X.NN ^ e := by
  have := mul_pow_le hn c 0 k hc
  simp only [pow_zero, mul_one, zero_add] at this
  exact le_trans this (pw_mono hn hke)

theorem n_le_pw1 : (X.n : ℤ) ≤ X.NN ^ 1 := by simpa using n_le_NN hn

theorem card_SJ : Fintype.card (SJ X.n) = 8 * X.n := by
  simp [SJ]; ring

theorem card_SJ_le : ((Fintype.card (SJ X.n) : ℕ) : ℤ) ≤ X.NN ^ 3 := by
  rw [card_SJ hn]
  have h1 : (X.n : ℤ) ≤ X.NN := n_le_NN hn
  have h4 := NN_ge_four hn
  have : X.NN ^ 3 = X.NN * X.NN * X.NN := by ring
  push_cast
  nlinarith

/-- a sum over state jobs of terms bounded by `N^e` is at most `N^(e+3)` -/
theorem sum_SJ_le (g : SJ X.n → ℤ) (e : ℕ) (h : ∀ s, g s ≤ X.NN ^ e) :
    ∑ s, g s ≤ X.NN ^ (e + 3) := by
  have := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset (SJ X.n))) => h s)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  have hc := card_SJ_le hn
  have : ((Fintype.card (SJ X.n) : ℕ) : ℤ) * X.NN ^ e ≤ X.NN ^ 3 * X.NN ^ e :=
    mul_le_mul_of_nonneg_right hc (pw_nonneg hn e)
  rw [show X.NN ^ (e + 3) = X.NN ^ 3 * X.NN ^ e by ring]
  linarith

theorem sum_blocks_le (g : Fin X.n → ℤ) (e : ℕ) (h : ∀ v, g v ≤ X.NN ^ e) :
    ∑ v, g v ≤ X.NN ^ (e + 1) := by
  have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin X.n))) => h v)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have : (X.n : ℤ) * X.NN ^ e ≤ X.NN ^ 1 * X.NN ^ e :=
    mul_le_mul_of_nonneg_right (n_le_pw1 hn) (pw_nonneg hn e)
  rw [show X.NN ^ (e + 1) = X.NN ^ 1 * X.NN ^ e by ring]
  linarith

/-! ### the chain of bounds -/

theorem P_le (v : Fin X.n) (h : Fin 4) : X.P v h + 3 ≤ X.NN ^ 51 := by
  unfold P
  have hht : (X.ht v h : ℤ) ≤ X.n := by exact_mod_cast X.ht_le v h
  have hM := X.M_pos
  have h1 : X.M * X.ht v h ≤ X.NN ^ 41 := by
    rw [M_eq, show X.NN ^ 41 = X.NN ^ 40 * X.NN ^ 1 by ring]
    exact mul_le_mul (le_refl _) (le_trans hht (n_le_pw1 hn)) (by positivity) (pw_nonneg hn 40)
  have h2 : Qc h + 3 ≤ X.NN ^ 41 := by
    have := Qc_le h
    have := const_le_pw hn 10003 7 41 (by norm_num) (by norm_num)
    linarith
  have h3 : X.NN ^ 41 ≤ X.NN ^ 50 := pw_mono hn (by norm_num)
  have h4 : 4 * X.NN ^ 50 ≤ X.NN ^ 51 := by
    have := mul_pow_le hn 4 50 1 (by norm_num); simpa using this
  have h5 := pw_nonneg hn 50
  rw [T_eq]
  linarith

theorem pS_le (s : SJ X.n) : X.pS s ≤ X.NN ^ 51 := by
  have := P_le hn s.1 s.2.1
  unfold pS; have := cA_le s.2.1; split_ifs <;> linarith [X.P_pos s.1 s.2.1]

theorem β_le (v : Fin X.n) : X.β v ≤ X.NN ^ 52 := by
  have := (β_bounds hn v).2
  have h : 5 * X.T ≤ X.NN ^ 52 := by
    have := mul_pow_le hn 5 50 2 (by norm_num); rw [T_eq]; simpa using this
  linarith

theorem lam_le' (v : Fin X.n) : X.lam v ≤ X.NN ^ 21 := by
  have := X.lam_le v
  have h1 : (X.n : ℤ) ≤ X.NN ^ 20 := le_trans (n_le_pw1 hn) (pw_mono hn (by norm_num))
  have := add_le_pw hn 21 (by norm_num) (le_of_eq (G_eq X)) h1
  linarith

theorem K_le' (u v : Fin X.n) : X.K u v ≤ X.NN ^ 22 := by
  have h1 : X.K u v ≤ X.L u := min_le_left _ _
  have h2 : X.L u = X.lam u + X.lam u := by unfold L; ring
  have := add_le_pw hn 22 (by norm_num) (lam_le' hn u) (lam_le' hn u)
  linarith

theorem f_le (v : Fin X.n) : X.f v ≤ X.NN ^ 75 := by
  unfold f
  have h : ∀ u, X.K v u * X.β u ≤ X.NN ^ 74 := fun u =>
    mul_le_pw hn 74 (by norm_num) (X.K_pos v u).le (K_le' hn v u) (X.β_pos u).le (β_le hn u)
  exact sum_blocks_le hn _ 74 h

theorem rS_le (s : SJ X.n) : X.rS s ≤ X.NN ^ 76 := by
  unfold rS
  have h1 := f_le hn s.1
  have h2 : X.lam s.1 * X.pS s ≤ X.NN ^ 72 :=
    mul_le_pw hn 72 (by norm_num) (X.lam_pos s.1).le (lam_le' hn s.1) (X.pS_pos s).le (pS_le hn s)
  exact add_le_pw hn 76 (by norm_num) h1 (le_trans h2 (pw_mono hn (by norm_num)))

theorem wES_le (s : SJ X.n) : X.wES s ≤ X.NN ^ 127 :=
  mul_le_pw hn 127 (by norm_num) (X.pS_pos s).le (pS_le hn s) (X.rS_pos s).le (rS_le hn s)

theorem α_le (s t : SJ X.n) : X.α s t ≤ X.NN ^ 178 := by
  have : X.α s t ≤ X.pS t * X.wES s := min_le_left _ _
  have := mul_le_pw hn 178 (by norm_num) (X.pS_pos t).le (pS_le hn t) (X.wES_pos s).le
    (wES_le hn s)
  linarith

theorem ρ_bounds (v : Fin X.n) (h : Fin 4) : 0 ≤ X.ρ v h ∧ X.ρ v h ≤ X.NN ^ 76 := by
  unfold ρ
  have hP := P_le hn v h
  have hc := cA_le h
  have hPp := X.P_pos v h
  have hcp := cA_pos h
  have h2 : 2 * X.P v h + cA h ≤ X.NN ^ 52 := by
    have := add_le_pw hn 52 (by norm_num) (show X.P v h + 3 ≤ X.NN ^ 51 from hP) hP
    linarith
  have h3 : X.lam v * (2 * X.P v h + cA h) ≤ X.NN ^ 73 :=
    mul_le_pw hn 73 (by norm_num) (X.lam_pos v).le (lam_le' hn v) (by linarith) h2
  constructor
  · have := X.f_nonneg v; have := X.lam_pos v; nlinarith
  · exact add_le_pw hn 76 (by norm_num) (f_le hn v) (le_trans h3 (pw_mono hn (by norm_num)))

theorem lo_bounds (η : ℕ) : 0 ≤ X.lo η ∧ X.lo η ≤ X.NN ^ 76 := by
  unfold lo
  split_ifs with hne
  · obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (s := X.atomsAt η) hne (fun a => X.ρ a.1 a.2)
    rw [ha]; exact ρ_bounds hn a.1 a.2
  · exact ⟨le_refl 0, pw_nonneg hn 76⟩

theorem hi_bounds (η : ℕ) : 0 ≤ X.hi η ∧ X.hi η ≤ X.NN ^ 76 := by
  unfold hi
  split_ifs with hne
  · obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' (s := X.atomsAt η) hne (fun a => X.ρ a.1 a.2)
    rw [ha]; exact ρ_bounds hn a.1 a.2
  · exact ⟨le_refl 0, pw_nonneg hn 76⟩

theorem abs_Δ_le (k : ℕ) : |X.Δ k| ≤ X.NN ^ 76 := by
  unfold Δ gap
  have := lo_bounds hn (X.n - k + 1)
  have := hi_bounds hn (X.n - k)
  rw [abs_le]; constructor <;> linarith

theorem dpre_le (v : Fin X.n) (k : ℕ) : X.dpre v k ≤ 3 := by
  unfold dpre
  calc _ ≤ (univ : Finset (Fin 3)).card := Finset.card_filter_le _ _
    _ = 3 := by simp

end size

end RXC3
end AWET

namespace AWET
namespace RXC3
variable {X : RXC3}

section size2
variable (hn : 0 < X.n)
include hn

theorem pwQ (e : ℕ) : ((X.NN ^ e : ℤ) : ℚ) = (X.NN : ℚ) ^ e := by push_cast; rfl

theorem pwQ_nonneg (e : ℕ) : (0:ℚ) ≤ (X.NN : ℚ) ^ e := by
  have := pw_nonneg hn e; exact_mod_cast this

theorem pwQ_mono {a b : ℕ} (h : a ≤ b) : (X.NN : ℚ) ^ a ≤ (X.NN : ℚ) ^ b := by
  have := pw_mono hn h; exact_mod_cast this

theorem sum_SJ_α_le (s : SJ X.n) : ∑ t : SJ X.n, X.α s t ≤ X.NN ^ 181 :=
  sum_SJ_le hn _ 178 (fun t => α_le hn s t)

theorem abs_a0_le (v : Fin X.n) : |X.a0 v| ≤ (X.NN : ℚ) ^ 182 := by
  rw [X.a0_eq]
  have hterm : ∀ a : Fin 4 × Bool, |(eps a.1 a.2 : ℚ) * ((∑ t : SJ X.n, (X.α (v, a) t : ℚ))
      - X.α (v, a) (v, a))| ≤ (X.NN : ℚ) ^ 181 := by
    intro a
    have h1 : (∑ t : SJ X.n, (X.α (v, a) t : ℚ)) ≤ (X.NN : ℚ) ^ 181 := by
      have := sum_SJ_α_le hn (v, a); rw [← pwQ hn]; exact_mod_cast this
    have h2 : (X.α (v, a) (v, a) : ℚ) ≤ ∑ t : SJ X.n, (X.α (v, a) t : ℚ) :=
      Finset.single_le_sum (f := fun t => (X.α (v, a) t : ℚ))
        (fun t _ => by exact_mod_cast (X.α_pos (v, a) t).le) (mem_univ (v, a))
    have h3 : (0:ℚ) < X.α (v, a) (v, a) := by exact_mod_cast X.α_pos (v, a) (v, a)
    have he : |(eps a.1 a.2 : ℚ)| = 1 := by
      rcases eps_cases a.1 a.2 with h | h <;> rw [h] <;> simp
    rw [abs_mul, he, one_mul, abs_le]
    constructor <;> linarith
  have hsum : |∑ a : Fin 4 × Bool, (eps a.1 a.2 : ℚ) * ((∑ t : SJ X.n, (X.α (v, a) t : ℚ))
      - X.α (v, a) (v, a))| ≤ 8 * (X.NN : ℚ) ^ 181 := by
    calc _ ≤ ∑ a : Fin 4 × Bool, |(eps a.1 a.2 : ℚ) * ((∑ t : SJ X.n, (X.α (v, a) t : ℚ))
            - X.α (v, a) (v, a))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin 4 × Bool, (X.NN : ℚ) ^ 181 := Finset.sum_le_sum (fun a _ => hterm a)
      _ = 8 * (X.NN : ℚ) ^ 181 := by
          rw [Finset.sum_const, Finset.card_univ]; simp
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℚ) < 1/4)]
  have h4i : 2 * X.NN ^ 181 ≤ X.NN ^ 182 := by
    have := mul_pow_le hn 2 181 1 (by norm_num); simpa using this
  have h4 : 2 * (X.NN : ℚ) ^ 181 ≤ (X.NN : ℚ) ^ 182 := by exact_mod_cast h4i
  linarith

theorem abs_astar_le (v : Fin X.n) : |X.astar v| ≤ (X.NN : ℚ) ^ 79 := by
  unfold astar
  have hterm : ∀ k ∈ Icc 1 X.n, |(X.Δ k : ℚ) * k * X.dpre v k| ≤ 3 * (X.NN : ℚ) ^ 77 := by
    intro k hk
    have hkn : (k : ℚ) ≤ X.NN := by
      have := (Finset.mem_Icc.mp hk).2
      have h := n_le_NN hn
      have : (k : ℤ) ≤ X.NN := le_trans (by exact_mod_cast this) h
      exact_mod_cast this
    have hΔ : |(X.Δ k : ℚ)| ≤ (X.NN : ℚ) ^ 76 := by
      have := abs_Δ_le hn k; rw [← pwQ hn]; exact_mod_cast this
    have hd : (X.dpre v k : ℚ) ≤ 3 := by exact_mod_cast dpre_le hn v k
    have hk0 : (0:ℚ) ≤ k := by positivity
    have hd0 : (0:ℚ) ≤ X.dpre v k := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hd0]
    have hN0 : (0:ℚ) ≤ X.NN := by exact_mod_cast (Npos hn).le
    calc |(X.Δ k : ℚ)| * k * X.dpre v k ≤ (X.NN : ℚ) ^ 76 * X.NN * 3 := by
          apply mul_le_mul _ hd hd0 (by positivity)
          exact mul_le_mul hΔ hkn hk0 (pwQ_nonneg hn 76)
      _ = 3 * (X.NN : ℚ) ^ 77 := by ring
  have hcard : ((Icc 1 X.n).card : ℚ) ≤ X.NN := by
    simp; have := n_le_NN hn; exact_mod_cast this
  have hsum : |∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * k * X.dpre v k| ≤ 3 * (X.NN : ℚ) ^ 78 := by
    calc _ ≤ ∑ k ∈ Icc 1 X.n, |(X.Δ k : ℚ) * k * X.dpre v k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 X.n, 3 * (X.NN : ℚ) ^ 77 := Finset.sum_le_sum hterm
      _ = ((Icc 1 X.n).card : ℚ) * (3 * (X.NN : ℚ) ^ 77) := by simp
      _ ≤ X.NN * (3 * (X.NN : ℚ) ^ 77) :=
          mul_le_mul_of_nonneg_right hcard (by have := pwQ_nonneg hn 77; positivity)
      _ = 3 * (X.NN : ℚ) ^ 78 := by ring
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℚ) < 1/4)]
  have h1 : (X.NN : ℚ) ^ 78 ≤ (X.NN : ℚ) ^ 79 := pwQ_mono hn (by norm_num)
  have h2 := pwQ_nonneg hn 78
  nlinarith

theorem Dv_ge (v : Fin X.n) : X.NN ^ 40 ≤ X.Dv v := by
  rw [Dv_eq']
  have p1 := X.ht_pos v 1 (by decide)
  have p2 := X.ht_pos v 2 (by decide)
  have p3 := X.ht_pos v 3 (by decide)
  have hM := X.M_pos
  have : (3:ℤ) ≤ (X.ht v 1 : ℤ) + X.ht v 2 + X.ht v 3 := by omega
  rw [← M_eq]
  nlinarith

theorem Dv_le' (v : Fin X.n) : X.Dv v ≤ X.NN ^ 44 := by
  have h := X.Dv_le v
  have h1 : 6 * (X.n : ℤ) * X.M ≤ X.NN ^ 43 := by
    have hnM : (X.n : ℤ) * X.M ≤ X.NN ^ 41 :=
      mul_le_pw hn 41 (by norm_num) (by positivity) (n_le_pw1 hn) X.M_pos.le (le_of_eq (M_eq X))
    have h6 : 6 * X.NN ^ 41 ≤ X.NN ^ 43 := by
      have := mul_pow_le hn 6 41 2 (by norm_num); simpa using this
    have e : 6 * (X.n : ℤ) * X.M = 6 * ((X.n : ℤ) * X.M) := by ring
    rw [e]; linarith
  have h2 : (22134 : ℤ) ≤ X.NN ^ 43 := const_le_pw hn 22134 8 43 (by norm_num) (by norm_num)
  exact add_le_pw hn 44 (by norm_num) h1 h2 |> le_trans h

theorem abs_eta_le (v : Fin X.n) : |X.eta v| ≤ X.NN ^ 144 := by
  have hD : ((X.NN : ℚ)) ^ 40 ≤ X.Dv v := by
    have := Dv_ge hn v; rw [← pwQ hn]; exact_mod_cast this
  have hDpos : (0:ℚ) < X.Dv v := by exact_mod_cast X.Dv_pos v
  set z : ℚ := (4 * (X.a0 v - X.astar v)) / (X.Dv v : ℚ) with hz
  have hr := abs_sub_round z
  have heta : (X.eta v : ℚ) = round z := by unfold eta; rw [← hz]
  have ha := abs_a0_le hn v
  have hs := abs_astar_le hn v
  have h79 : (X.NN : ℚ) ^ 79 ≤ (X.NN : ℚ) ^ 182 := pwQ_mono hn (by norm_num)
  have hnum : |4 * (X.a0 v - X.astar v)| ≤ 8 * (X.NN : ℚ) ^ 182 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℚ) < 4)]
    have := abs_sub (X.a0 v) (X.astar v)
    linarith
  have hzb : |z| ≤ 8 * (X.NN : ℚ) ^ 142 := by
    rw [hz, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have e : (X.NN : ℚ) ^ 182 = (X.NN : ℚ) ^ 142 * (X.NN : ℚ) ^ 40 := by ring
    have h142 := pwQ_nonneg hn 142
    calc |4 * (X.a0 v - X.astar v)| ≤ 8 * (X.NN : ℚ) ^ 182 := hnum
      _ = 8 * (X.NN : ℚ) ^ 142 * (X.NN : ℚ) ^ 40 := by rw [e]; ring
      _ ≤ 8 * (X.NN : ℚ) ^ 142 * X.Dv v := mul_le_mul_of_nonneg_left hD (by positivity)
  have hη : |(X.eta v : ℚ)| ≤ 8 * (X.NN : ℚ) ^ 142 + 1 := by
    rw [heta]
    have h2 := abs_sub z (z - (round z : ℚ))
    rw [show z - (z - (round z : ℚ)) = (round z : ℚ) by ring] at h2
    linarith
  have h16 : 16 * (X.NN : ℚ) ^ 142 ≤ (X.NN : ℚ) ^ 144 := by
    have := mul_pow_le hn 16 142 2 (by norm_num); rw [← pwQ hn]; exact_mod_cast this
  have h1 : (1:ℚ) ≤ (X.NN : ℚ) ^ 142 := by
    have := const_le_pw hn 1 0 142 (by norm_num) (by norm_num); rw [← pwQ hn]; exact_mod_cast this
  have : |(X.eta v : ℚ)| ≤ (X.NN : ℚ) ^ 144 := by linarith
  rw [← pwQ hn] at this
  exact_mod_cast this

theorem etamax_le : X.etamax ≤ X.NN ^ 144 := by
  unfold etamax
  have hne : (univ : Finset (Fin X.n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin X.n)) hne
    (fun v => (X.eta v).natAbs)
  rw [hv]
  have := abs_eta_le hn v
  rw [Int.abs_eq_natAbs] at this
  exact this

theorem abs_etabar_le (s t : SJ X.n) : |X.etabar s t| ≤ X.NN ^ 144 := by
  unfold etabar; split_ifs
  · exact abs_eta_le hn _
  · exact abs_eta_le hn _

end size2

end RXC3
end AWET

namespace AWET
namespace RXC3
variable {X : RXC3}

theorem ite_le_of_nonneg {p : Prop} [Decidable p] {x b : ℤ} (hx : 0 ≤ x) (hb : x ≤ b) :
    (if p then x else 0) ≤ b := by
  split_ifs
  · exact hb
  · exact le_trans hx hb

section size3
variable (hn : 0 < X.n)
include hn

theorem pS_sq_le (s : SJ X.n) : X.pS s ^ 2 ≤ X.NN ^ 102 := by
  rw [sq]; exact mul_le_pw hn 102 (by norm_num) (X.pS_pos s).le (pS_le hn s) (X.pS_pos s).le
    (pS_le hn s)

theorem U_le : X.U ≤ X.NN ^ 253 := by
  unfold U
  have S1 : (∑ i : SJ X.n, ∑ j : SJ X.n, if encS i < encS j then X.α i j else 0) ≤ X.NN ^ 252 := by
    have := sum_SJ_le hn (fun i => ∑ j : SJ X.n, if encS i < encS j then X.α i j else 0) 181
      (fun i => by
        have := sum_SJ_le hn (fun j => if encS i < encS j then X.α i j else 0) 178
          (fun j => ite_le_of_nonneg (X.α_pos i j).le (α_le hn i j))
        exact le_trans this (pw_mono hn (by norm_num)))
    exact le_trans this (pw_mono hn (by norm_num))
  have S2 : (∑ i : SJ X.n, |X.eta i.1| * X.pS i ^ 2) ≤ X.NN ^ 252 := by
    have := sum_SJ_le hn (fun i => |X.eta i.1| * X.pS i ^ 2) 246
      (fun i => mul_le_pw hn 246 (by norm_num) (abs_nonneg _) (abs_eta_le hn i.1)
        (by positivity) (pS_sq_le hn i))
    exact le_trans this (pw_mono hn (by norm_num))
  have S3 : (∑ i : SJ X.n, ∑ j : SJ X.n,
      if encS i < encS j then |X.etabar i j| * X.pS i * X.pS j else 0) ≤ X.NN ^ 252 := by
    exact sum_SJ_le hn _ 249 (fun i => by
      have := sum_SJ_le hn (fun j => if encS i < encS j then |X.etabar i j| * X.pS i * X.pS j
          else 0) 246 (fun j => by
            have h1 : |X.etabar i j| * X.pS i ≤ X.NN ^ 195 :=
              mul_le_pw hn 195 (by norm_num) (abs_nonneg _) (abs_etabar_le hn i j)
                (X.pS_pos i).le (pS_le hn i)
            have h2 : |X.etabar i j| * X.pS i * X.pS j ≤ X.NN ^ 246 :=
              mul_le_pw hn 246 (by norm_num) (mul_nonneg (abs_nonneg _) (X.pS_pos i).le) h1
                (X.pS_pos j).le (pS_le hn j)
            exact ite_le_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (X.pS_pos i).le)
              (X.pS_pos j).le) h2)
      exact this)
  have h1 : (1:ℤ) ≤ X.NN ^ 252 := const_le_pw hn 1 0 252 (by norm_num) (by norm_num)
  have h4 : 4 * X.NN ^ 252 ≤ X.NN ^ 253 := by
    have := mul_pow_le hn 4 252 1 (by norm_num); simpa using this
  linarith

theorem H_le : X.H ≤ X.NN ^ 254 := by
  unfold H
  have h1 := U_le hn
  have h2 := etamax_le hn
  have h3 : X.NN ^ 144 ≤ X.NN ^ 253 := pw_mono hn (by norm_num)
  have h4 : (2:ℤ) ≤ X.NN ^ 253 := const_le_pw hn 2 1 253 (by norm_num) (by norm_num)
  have h5 : 4 * X.NN ^ 253 ≤ X.NN ^ 254 := by
    have := mul_pow_le hn 4 253 1 (by norm_num); simpa using this
  linarith

theorem L_le' (u : Fin X.n) : X.L u ≤ X.NN ^ 22 := by
  have h2 : X.L u = X.lam u + X.lam u := by unfold L; ring
  have := add_le_pw hn 22 (by norm_num) (lam_le' hn u) (lam_le' hn u)
  linarith

theorem sS_le (s : SJ X.n) : X.sS s ≤ X.NN ^ 277 := by
  unfold sS
  have h1 : X.H * X.L s.1 ≤ X.NN ^ 276 :=
    mul_le_pw hn 276 (by norm_num) X.H_pos.le (H_le hn) (X.L_pos s.1).le (L_le' hn s.1)
  have h2 : X.eta s.1 ≤ X.NN ^ 276 :=
    le_trans (le_abs_self _) (le_trans (abs_eta_le hn s.1) (pw_mono hn (by norm_num)))
  exact add_le_pw hn 277 (by norm_num) h1 h2

theorem wLS_le (s : SJ X.n) : X.wLS s ≤ X.NN ^ 328 :=
  mul_le_pw hn 328 (by norm_num) (X.pS_pos s).le (pS_le hn s) (X.sS_pos s).le (sS_le hn s)

theorem rmax_le : X.rmax ≤ X.NN ^ 76 := by
  unfold rmax
  have hne : (univ : Finset (SJ X.n)).Nonempty := ⟨(⟨0, hn⟩, 0, false), mem_univ _⟩
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup (univ : Finset (SJ X.n)) hne
    (fun i => (X.rS i).toNat)
  rw [hs]
  have h2 : ((X.rS s).toNat : ℤ) = X.rS s := Int.toNat_of_nonneg (X.rS_pos s).le
  rw [h2]; exact rS_le hn s

theorem wEJ_anchor_le : X.H * (1 + X.rmax) ≤ X.NN ^ 331 := by
  have h1 : 1 + X.rmax ≤ X.NN ^ 77 := by
    have := rmax_le hn
    have h2 : (1:ℤ) ≤ X.NN ^ 76 := const_le_pw hn 1 0 76 (by norm_num) (by norm_num)
    exact add_le_pw hn 77 (by norm_num) h2 this
  exact mul_le_pw hn 331 (by norm_num) X.H_pos.le (H_le hn) (by linarith [X.rmax_nonneg]) h1

theorem τ_le (s t : SJ X.n) : X.τ s t ≤ X.NN ^ 379 := by
  have : X.τ s t ≤ X.pS t * X.wLS s := min_le_left _ _
  have h := mul_le_pw hn 379 (by norm_num) (X.pS_pos t).le (pS_le hn t) (X.wLS_pos s).le
    (wLS_le hn s)
  linarith

theorem τ_pos (s t : SJ X.n) : 0 < X.τ s t := by
  unfold τ; have := X.pS_pos s; have := X.pS_pos t; have := X.wLS_pos s; have := X.wLS_pos t
  exact lt_min (by positivity) (by positivity)

theorem Cstar_le : X.Cstar ≤ X.NN ^ 387 := by
  unfold Cstar
  rw [X.Φ_anchor_early X.agrees_pre (X.mem_codedE_anchor _)]
  have S1 : (∑ s : SJ X.n, if Job.st s ∈ X.codedE (fun _ => true) then X.H * X.wES s else 0)
      ≤ X.NN ^ 384 :=
    sum_SJ_le hn _ 381 (fun s => ite_le_of_nonneg (mul_pos X.H_pos (X.wES_pos s)).le
      (mul_le_pw hn 381 (by norm_num) X.H_pos.le (H_le hn) (X.wES_pos s).le (wES_le hn s)))
  have S2 : (∑ s : SJ X.n, ∑ t : SJ X.n, if encS s < encS t then
      ((if Job.st s ∈ X.codedE (fun _ => true) ∧ Job.st t ∈ X.codedE (fun _ => true)
        then X.α s t else 0)
      + (if Job.st s ∉ X.codedE (fun _ => true) ∧ Job.st t ∉ X.codedE (fun _ => true)
        then X.τ s t else 0)) else 0) ≤ X.NN ^ 386 := by
    refine sum_SJ_le hn _ 383 (fun s => sum_SJ_le hn _ 380 (fun t => ?_))
    have ha : X.α s t ≤ X.NN ^ 379 := le_trans (α_le hn s t) (pw_mono hn (by norm_num))
    have hb := τ_le hn s t
    have hab : X.α s t + X.τ s t ≤ X.NN ^ 380 := add_le_pw hn 380 (by norm_num) ha hb
    have h0a := (X.α_pos s t).le
    have h0b := (τ_pos hn s t).le
    split_ifs <;> linarith
  have S3 : (∑ s : SJ X.n, if Job.st s ∈ X.codedE (fun _ => true) then 0
      else X.pS s * X.wLS s) ≤ X.NN ^ 386 := by
    refine sum_SJ_le hn _ 383 (fun s => ?_)
    have := mul_le_pw hn 383 (by norm_num) (X.pS_pos s).le (pS_le hn s) (X.wLS_pos s).le
      (wLS_le hn s)
    have h0 := (mul_pos (X.pS_pos s) (X.wLS_pos s)).le
    split_ifs <;> linarith [pw_nonneg hn 383]
  have h1 : X.NN ^ 384 ≤ X.NN ^ 386 := pw_mono hn (by norm_num)
  have h4 : 4 * X.NN ^ 386 ≤ X.NN ^ 387 := by
    have := mul_pow_le hn 4 386 1 (by norm_num); simpa using this
  have := pw_nonneg hn 386
  linarith

theorem sa_le : X.sa ≤ X.NN ^ 388 := by
  unfold sa
  have hC := X.Cstar_nonneg
  have hH : (1:ℚ) ≤ (X.H : ℚ) ^ 2 := by
    have : (1:ℤ) ≤ X.H := X.H_pos
    have : (1:ℤ) ≤ X.H ^ 2 := by nlinarith
    exact_mod_cast this
  have hq : (X.Cstar : ℚ) / (X.H : ℚ) ^ 2 ≤ X.Cstar := by
    rw [div_le_iff₀ (by linarith)]
    have : (0:ℚ) ≤ X.Cstar := by exact_mod_cast hC
    nlinarith
  have hc := Int.ceil_lt_add_one ((X.Cstar : ℚ) / (X.H : ℚ) ^ 2)
  have hceil : ⌈(X.Cstar : ℚ) / (X.H : ℚ) ^ 2⌉ ≤ X.Cstar + 1 := by
    have : ((⌈(X.Cstar : ℚ) / (X.H : ℚ) ^ 2⌉ : ℤ) : ℚ) < X.Cstar + 1 := by linarith
    have : ⌈(X.Cstar : ℚ) / (X.H : ℚ) ^ 2⌉ < X.Cstar + 1 := by exact_mod_cast this
    linarith
  have h1 := Cstar_le hn
  have h2 : (2:ℤ) ≤ X.NN ^ 387 := const_le_pw hn 2 1 387 (by norm_num) (by norm_num)
  have := add_le_pw hn 388 (by norm_num) h1 h2
  linarith

theorem wL_anchor_le : X.H * X.sa ≤ X.NN ^ 642 :=
  mul_le_pw hn 642 (by norm_num) X.H_pos.le (H_le hn) X.sa_pos.le (sa_le hn)

end size3

end RXC3
end AWET

namespace AWET
namespace RXC3
variable {X : RXC3}

section size4
variable (hn : 0 < X.n)
include hn

theorem pwQ_le {a b : ℕ} (h : a ≤ b) : (X.NN : ℚ) ^ a ≤ (X.NN : ℚ) ^ b := pwQ_mono hn h

theorem addQ_le {a b : ℚ} {e0 : ℕ} (e : ℕ) (he : e0 < e) (ha : a ≤ (X.NN : ℚ) ^ e0)
    (hb : b ≤ (X.NN : ℚ) ^ e0) : a + b ≤ (X.NN : ℚ) ^ e := by
  have h2 : 2 * X.NN ^ e0 ≤ X.NN ^ (e0 + 1) := by
    have := mul_pow_le hn 2 e0 1 (by norm_num); simpa using this
  have h2' : 2 * (X.NN : ℚ) ^ e0 ≤ (X.NN : ℚ) ^ (e0 + 1) := by exact_mod_cast h2
  have h3 : (X.NN : ℚ) ^ (e0 + 1) ≤ (X.NN : ℚ) ^ e := pwQ_le hn (by omega)
  linarith

theorem abs_ev_le' (v : Fin X.n) : |X.ev v| ≤ (X.NN : ℚ) ^ 44 := by
  have h1 := X.abs_ev_le v
  have h2 : (X.Dv v : ℚ) ≤ (X.NN : ℚ) ^ 44 := by
    have := Dv_le' hn v; rw [← pwQ hn]; exact_mod_cast this
  have h3 : (0:ℚ) ≤ X.Dv v := by exact_mod_cast (X.Dv_pos v).le
  linarith

theorem abs_Jc_le (u v : Fin X.n) : |X.Jc u v| ≤ (X.NN : ℚ) ^ 180 := by
  unfold Jc
  have hterm : ∀ a b : Fin 4 × Bool,
      |(eps a.1 a.2 : ℚ) * eps b.1 b.2 * X.α (u, a) (v, b)| ≤ (X.NN : ℚ) ^ 178 := by
    intro a b
    have ha : |(eps a.1 a.2 : ℚ)| = 1 := by rcases eps_cases a.1 a.2 with h | h <;> rw [h] <;> simp
    have hb : |(eps b.1 b.2 : ℚ)| = 1 := by rcases eps_cases b.1 b.2 with h | h <;> rw [h] <;> simp
    rw [abs_mul, abs_mul, ha, hb, one_mul, one_mul]
    have h1 : (0:ℚ) ≤ X.α (u, a) (v, b) := by exact_mod_cast (X.α_pos _ _).le
    rw [abs_of_nonneg h1, ← pwQ hn]; exact_mod_cast α_le hn _ _
  have hs : |∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
      (eps a.1 a.2 : ℚ) * eps b.1 b.2 * X.α (u, a) (v, b)| ≤ 64 * (X.NN : ℚ) ^ 178 := by
    calc _ ≤ ∑ a : Fin 4 × Bool, |∑ b : Fin 4 × Bool,
            (eps a.1 a.2 : ℚ) * eps b.1 b.2 * X.α (u, a) (v, b)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
            |(eps a.1 a.2 : ℚ) * eps b.1 b.2 * X.α (u, a) (v, b)| :=
          Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool, (X.NN : ℚ) ^ 178 :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm a b))
      _ = 64 * (X.NN : ℚ) ^ 178 := by simp; ring
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℚ) < 1/4)]
  have h16 : 16 * X.NN ^ 178 ≤ X.NN ^ 180 := by
    have := mul_pow_le hn 16 178 2 (by norm_num); simpa using this
  have h16' : 16 * (X.NN : ℚ) ^ 178 ≤ (X.NN : ℚ) ^ 180 := by exact_mod_cast h16
  linarith

theorem sumQ_blocks_le (g : Fin X.n → ℚ) (e : ℕ) (h : ∀ v, |g v| ≤ (X.NN : ℚ) ^ e) :
    |∑ v, g v| ≤ (X.NN : ℚ) ^ (e + 1) := by
  have hN : ((X.n : ℕ) : ℚ) ≤ (X.NN : ℚ) := by have := n_le_NN hn; exact_mod_cast this
  calc |∑ v, g v| ≤ ∑ v, |g v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v : Fin X.n, (X.NN : ℚ) ^ e := Finset.sum_le_sum (fun v _ => h v)
    _ = (X.n : ℚ) * (X.NN : ℚ) ^ e := by simp
    _ ≤ (X.NN : ℚ) * (X.NN : ℚ) ^ e := mul_le_mul_of_nonneg_right hN (pwQ_nonneg hn e)
    _ = (X.NN : ℚ) ^ (e + 1) := by ring

theorem abs_C0_le : |X.C0| ≤ (X.NN : ℚ) ^ 388 := by
  unfold C0
  have hC : |(X.Cstar : ℚ)| ≤ (X.NN : ℚ) ^ 387 := by
    rw [abs_of_nonneg (by exact_mod_cast X.Cstar_nonneg), ← pwQ hn]
    exact_mod_cast Cstar_le hn
  have h1 : |∑ v, (X.astar v + X.ev v)| ≤ (X.NN : ℚ) ^ 81 := by
    apply sumQ_blocks_le hn _ 80
    intro v
    have := abs_add_le (X.astar v) (X.ev v)
    have h79 := abs_astar_le hn v
    have h44 := abs_ev_le' hn v
    have : (X.NN : ℚ) ^ 44 ≤ (X.NN : ℚ) ^ 79 := pwQ_le hn (by norm_num)
    have := addQ_le hn 80 (show 79 < 80 by norm_num) h79 (by linarith : |X.ev v| ≤ (X.NN : ℚ) ^ 79)
    linarith
  have h2 : |∑ u, ∑ v, if u < v then X.Jc u v else 0| ≤ (X.NN : ℚ) ^ 182 := by
    apply sumQ_blocks_le hn _ 181
    intro u
    apply sumQ_blocks_le hn _ 180
    intro v
    split_ifs
    · exact abs_Jc_le hn u v
    · simp; exact pwQ_nonneg hn 180
  have h3 := abs_sub (X.Cstar - ∑ v, (X.astar v + X.ev v) : ℚ) (∑ u, ∑ v, if u < v then X.Jc u v else 0)
  have h4 := abs_sub (X.Cstar : ℚ) (∑ v, (X.astar v + X.ev v))
  have e1 : (X.NN : ℚ) ^ 81 ≤ (X.NN : ℚ) ^ 387 := pwQ_le hn (by norm_num)
  have e2 : (X.NN : ℚ) ^ 182 ≤ (X.NN : ℚ) ^ 387 := pwQ_le hn (by norm_num)
  have e3 : 4 * X.NN ^ 387 ≤ X.NN ^ 388 := by
    have := mul_pow_le hn 4 387 1 (by norm_num); simpa using this
  have e3' : 4 * (X.NN : ℚ) ^ 387 ≤ (X.NN : ℚ) ^ 388 := by exact_mod_cast e3
  have := pwQ_nonneg hn 387
  linarith

theorem abs_Aconst_le : |X.Aconst| ≤ (X.NN : ℚ) ^ 389 := by
  unfold Aconst
  have hC := abs_C0_le hn
  have hterm : ∀ k ∈ Icc 1 X.n,
      |(X.Δ k : ℚ) * ((k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2)| ≤ (X.NN : ℚ) ^ 80 := by
    intro k hk
    have hkn : (k : ℚ) ≤ X.NN := by
      have := (Finset.mem_Icc.mp hk).2
      have h := n_le_NN hn
      have : (k : ℤ) ≤ X.NN := le_trans (by exact_mod_cast this) h
      exact_mod_cast this
    have hΔ : |(X.Δ k : ℚ)| ≤ (X.NN : ℚ) ^ 76 := by
      have := abs_Δ_le hn k; rw [← pwQ hn]; exact_mod_cast this
    have hd : ∑ v, (X.dpre v k : ℚ) ^ 2 ≤ 9 * X.NN := by
      have : ∀ v, (X.dpre v k : ℚ) ^ 2 ≤ 9 := by
        intro v
        have h1 : (X.dpre v k : ℚ) ≤ 3 := by exact_mod_cast dpre_le hn v k
        have h0 : (0:ℚ) ≤ X.dpre v k := by positivity
        nlinarith
      calc ∑ v, (X.dpre v k : ℚ) ^ 2 ≤ ∑ v : Fin X.n, (9:ℚ) := Finset.sum_le_sum (fun v _ => this v)
        _ = 9 * X.n := by simp; ring
        _ ≤ 9 * X.NN := by
            have := n_le_NN hn
            have : ((X.n : ℕ) : ℚ) ≤ (X.NN : ℚ) := by exact_mod_cast this
            linarith
    have hN4 : (X.NN : ℚ) ≥ 4 := by have := NN_ge_four hn; exact_mod_cast this
    have hpos : (0:ℚ) ≤ (k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2 := by positivity
    have hk0 : (0:ℚ) ≤ k := by positivity
    have hsum : (k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2 ≤ (X.NN : ℚ) ^ 4 := by
      have hk2 : (k : ℚ) ^ 2 ≤ (X.NN : ℚ) ^ 2 := pow_le_pow_left₀ hk0 hkn 2
      have hN2 : (16:ℚ) ≤ (X.NN : ℚ) ^ 2 := by nlinarith
      have hN4' : (X.NN : ℚ) ^ 4 = (X.NN : ℚ) ^ 2 * (X.NN : ℚ) ^ 2 := by ring
      have h9 : 9 * (X.NN : ℚ) ≤ 15 * (X.NN : ℚ) ^ 2 := by nlinarith
      nlinarith
    rw [abs_mul, abs_of_nonneg hpos]
    calc |(X.Δ k : ℚ)| * ((k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2)
        ≤ (X.NN : ℚ) ^ 76 * (X.NN : ℚ) ^ 4 := mul_le_mul hΔ hsum hpos (pwQ_nonneg hn 76)
      _ = (X.NN : ℚ) ^ 80 := by ring
  have hsum : |∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * ((k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2)|
      ≤ (X.NN : ℚ) ^ 81 := by
    have hcard : ((Icc 1 X.n).card : ℚ) ≤ X.NN := by
      simp; have := n_le_NN hn; exact_mod_cast this
    calc _ ≤ ∑ k ∈ Icc 1 X.n, |(X.Δ k : ℚ) * ((k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 X.n, (X.NN : ℚ) ^ 80 := Finset.sum_le_sum hterm
      _ = ((Icc 1 X.n).card : ℚ) * (X.NN : ℚ) ^ 80 := by simp
      _ ≤ X.NN * (X.NN : ℚ) ^ 80 := mul_le_mul_of_nonneg_right hcard (pwQ_nonneg hn 80)
      _ = (X.NN : ℚ) ^ 81 := by ring
  set S := ∑ k ∈ Icc 1 X.n, (X.Δ k : ℚ) * ((k : ℚ) ^ 2 + ∑ v, (X.dpre v k : ℚ) ^ 2) with hS
  have h1 := abs_sub X.C0 ((1/8 : ℚ) * S)
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℚ) < 1/8)] at h1
  have e1 : (X.NN : ℚ) ^ 81 ≤ (X.NN : ℚ) ^ 388 := pwQ_le hn (by norm_num)
  have h2 : (1/8 : ℚ) * |S| ≤ (X.NN : ℚ) ^ 388 := by
    have := abs_nonneg S
    linarith
  have := addQ_le hn 389 (show 388 < 389 by norm_num) hC h2
  linarith

theorem Gam_nonneg : 0 ≤ X.Gam := by
  unfold Gam
  have := X.W_nonneg hn
  have hW : (0:ℚ) ≤ X.W := by exact_mod_cast this
  have hD : (0:ℚ) ≤ ∑ v, (X.Dv v : ℚ) :=
    Finset.sum_nonneg (fun v _ => by exact_mod_cast (X.Dv_pos v).le)
  positivity

theorem abs_Bnd_le : |X.Bnd| ≤ X.NN ^ 391 := by
  have hA := abs_Aconst_le hn
  have hG0 := Gam_nonneg hn
  have hG := four_Gam_lt hn
  have hGM : (X.G : ℚ) * X.M = (X.NN : ℚ) ^ 60 := by rw [G_eq, M_eq]; push_cast; ring
  have hq : |X.Aconst + X.Gam| ≤ (X.NN : ℚ) ^ 390 := by
    have h1 : |X.Gam| ≤ (X.NN : ℚ) ^ 389 := by
      rw [abs_of_nonneg hG0]
      have : (X.NN : ℚ) ^ 60 ≤ (X.NN : ℚ) ^ 389 := pwQ_le hn (by norm_num)
      have := pwQ_nonneg hn 60
      linarith
    have := abs_add_le X.Aconst X.Gam
    have := addQ_le hn 390 (show 389 < 390 by norm_num) hA h1
    linarith
  unfold Bnd
  set q := X.Aconst + X.Gam
  have hf1 := Int.floor_le q
  have hf2 := Int.lt_floor_add_one q
  have hqq := abs_le.mp hq
  have h1 : (1:ℚ) ≤ (X.NN : ℚ) ^ 390 := by
    have := const_le_pw hn 1 0 390 (by norm_num) (by norm_num); rw [← pwQ hn]; exact_mod_cast this
  have h2i : 2 * X.NN ^ 390 ≤ X.NN ^ 391 := by
    have := mul_pow_le hn 2 390 1 (by norm_num); simpa using this
  have h2 : 2 * (X.NN : ℚ) ^ 390 ≤ (X.NN : ℚ) ^ 391 := by exact_mod_cast h2i
  have : |((⌊q⌋ : ℤ) : ℚ)| ≤ (X.NN : ℚ) ^ 391 := by
    rw [abs_le]; constructor <;> linarith
  rw [← pwQ hn] at this
  exact_mod_cast this

theorem d_le : X.inst.d ≤ X.NN ^ 258 := by
  unfold Inst.d
  rw [Job.sum_job]
  have h1 : X.inst.p Job.anchor ≤ X.NN ^ 257 := le_trans (H_le hn) (pw_mono hn (by norm_num))
  have h2 : ∑ s : SJ X.n, X.inst.p (Job.st s) ≤ X.NN ^ 257 :=
    le_trans (sum_SJ_le hn (fun s => X.inst.p (Job.st s)) 51 (fun s => pS_le hn s))
      (pw_mono hn (by norm_num))
  exact add_le_pw hn 258 (by norm_num) h1 h2

end size4

/-- **Lemma I.19 (polynomial and unary bounds).** The constructed instance has `8n + 1` jobs and
every integer it contains — processing times, earliness and tardiness weights, the due date
and the decision bound — is at most `(n+1)^650` in absolute value. -/
theorem size_bound (X : RXC3) (hn : 0 < X.n) :
    Fintype.card (Job X.n) = 8 * X.n + 1 ∧
    (∀ j, 0 < X.inst.p j ∧ X.inst.p j ≤ ((X.n : ℤ) + 1) ^ 650) ∧
    (∀ j, 0 < X.inst.wE j ∧ X.inst.wE j ≤ ((X.n : ℤ) + 1) ^ 650) ∧
    (∀ j, 0 < X.inst.wL j ∧ X.inst.wL j ≤ ((X.n : ℤ) + 1) ^ 650) ∧
    X.inst.d ≤ ((X.n : ℤ) + 1) ^ 650 ∧
    |X.Bnd| ≤ ((X.n : ℤ) + 1) ^ 650 := by
  have hN : X.NN = (X.n : ℤ) + 1 := rfl
  rw [← hN]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Fintype.card (Option (SJ X.n)) = _
    rw [Fintype.card_option, card_SJ hn]
  · intro j
    refine ⟨X.inst.hp j, ?_⟩
    rcases Job.cases j with rfl | ⟨s, rfl⟩
    · exact le_trans (H_le hn) (pw_mono hn (by norm_num))
    · exact le_trans (pS_le hn s) (pw_mono hn (by norm_num))
  · intro j
    refine ⟨X.inst.hwE j, ?_⟩
    rcases Job.cases j with rfl | ⟨s, rfl⟩
    · exact le_trans (wEJ_anchor_le hn) (pw_mono hn (by norm_num))
    · exact le_trans (wES_le hn s) (pw_mono hn (by norm_num))
  · intro j
    refine ⟨X.inst.hwL j, ?_⟩
    rcases Job.cases j with rfl | ⟨s, rfl⟩
    · exact le_trans (wL_anchor_le hn) (pw_mono hn (by norm_num))
    · exact le_trans (wLS_le hn s) (pw_mono hn (by norm_num))
  · exact le_trans (d_le hn) (pw_mono hn (by norm_num))
  · exact le_trans (abs_Bnd_le hn) (pw_mono hn (by norm_num))

end RXC3
end AWET


open Finset

namespace AWET

/-! ## 15. Summary: Part I of Hall–Kellerer–Song, machine-checked

* `Inst.yes_iff` — **Lemma I.3 + Proposition I.4**: the AWET decision problem (real-valued
  start times, one machine, `d = Σ p_j`) has a yes-answer iff some early set `E` has canonical
  cost `Φ(E) ≤ B`.  An early set is therefore a polynomial certificate (membership in NP).
* `RXC3.exactCover_iff_RPE` — **Lemmas I.7–I.9** (Reduction I).
* `RXC3.reduction_iff` — **Lemmas I.17–I.18** (Reduction II, via Lemmas I.11–I.16): the RXC3
  instance has an exact cover iff the constructed AWET instance has a schedule of cost `≤ B`.
* `RXC3.size_bound` — **Lemma I.19**: `8n+1` jobs, every number at most `(n+1)^650`.
-/

/-- **Theorem I.2 (formal core).** The paper's transformation `X ↦ (X.inst, X.Bnd)` from
Restricted Exact Cover by 3-Sets to AWET with the boundary due date `d = Σ p_j` is correct, and
for every nonempty source instance it uses `8n+1` jobs whose data, due date and threshold are
bounded by the fixed polynomial `(n+1)^650`. -/
theorem AWET_strong_reduction (X : RXC3) :
    (X.HasExactCover ↔ X.inst.Yes X.Bnd) ∧
    (0 < X.n →
      Fintype.card (Job X.n) = 8 * X.n + 1 ∧
      (∀ j, 0 < X.inst.p j ∧ X.inst.p j ≤ ((X.n : ℤ) + 1) ^ 650) ∧
      (∀ j, 0 < X.inst.wE j ∧ X.inst.wE j ≤ ((X.n : ℤ) + 1) ^ 650) ∧
      (∀ j, 0 < X.inst.wL j ∧ X.inst.wL j ≤ ((X.n : ℤ) + 1) ^ 650) ∧
      X.inst.d ≤ ((X.n : ℤ) + 1) ^ 650 ∧
      |X.Bnd| ≤ ((X.n : ℤ) + 1) ^ 650) :=
  ⟨X.reduction_iff, fun hn => RXC3.size_bound X hn⟩

end AWET

/-! ## 16. Sanity check against the paper's worked examples (Appendix B)

The definitions above reproduce the exact numbers printed in the paper's Appendix B, and the
main theorem settles both worked examples.  All checks are evaluated by the kernel (`decide`);
no `native_decide` is used. -/

namespace AWET.Examples

/-- The "yes" instance of Appendix B.1 (elements `e₁,…,e₆` are numbered `0,…,5`). -/
def exYes : RXC3 where
  n := 6
  S := ![![0, 1, 2], ![0, 1, 4], ![1, 3, 5], ![0, 2, 5], ![3, 4, 5], ![2, 3, 4]]
  mono := by decide
  reg := by decide

/-- The "no" instance of Appendix B.2 (`e₃` and `e₄` exchanged between `S₁` and `S₃`). -/
def exNo : RXC3 where
  n := 6
  S := ![![0, 1, 3], ![0, 1, 4], ![1, 2, 5], ![0, 2, 5], ![3, 4, 5], ![2, 3, 4]]
  mono := by decide
  reg := by decide

/-- block `v = 1` of the example (0-based index `0`) -/
def blk1 : Fin exYes.n := ⟨0, by decide⟩

/-- Table 10, first row: `P₁₁` and `β₁`. -/
theorem table10_P11 : exYes.P blk1 1 = 1798465080848246712074448255018260184595355 := by decide
theorem table10_beta1 : exYes.β blk1 = 7193860266091735000116541148400124485376124 := by decide

/-- Table 13: the first main gap `Δ₁`, the narrowest gap `Δ₄` and the total band width `W`. -/
theorem table13_gap1 : exYes.Δ 1 = 1016043624362133256191860470548001610280402871141813 := by
  decide
theorem table13_gap4 : exYes.Δ 4 = 1016043505663439397306514004527616836374161673142606 := by
  decide
theorem table13_W : exYes.W = 1122242198645248067609119549079725635487220872 := by decide

/-- B.1: `{S₁, S₅}` is an exact cover ... -/
theorem exYes_cover : exYes.IsExactCover ![true, false, false, false, true, false] := by
  unfold RXC3.IsExactCover; decide

/-- ... hence the constructed 49-job AWET instance has a schedule of cost at most `B`. -/
theorem exYes_yes : exYes.inst.Yes exYes.Bnd := exYes.reduction_iff.mp ⟨_, exYes_cover⟩

/-- B.2: the modified instance has no exact cover (all 64 selections fail) ... -/
theorem exNo_noCover : ¬ exNo.HasExactCover := by
  unfold RXC3.HasExactCover RXC3.IsExactCover; decide

/-- ... hence its constructed AWET instance has **no** schedule (with arbitrary real start
times) of cost at most `B`. -/
theorem exNo_no : ¬ exNo.inst.Yes exNo.Bnd := fun h => exNo_noCover (exNo.reduction_iff.mpr h)

end AWET.Examples

#print axioms AWET.AWET_strong_reduction
#print axioms AWET.Inst.yes_iff
#print axioms AWET.Examples.exNo_no
