import ACS12.PeanoFiniteConvex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Convexity passes through a complete finite Peano integral. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set
open scoped BigOperators

noncomputable def weightedFinitePeano (a : ℝ) (w : ℝ → ℝ) (N : ℕ) (p : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, w t * finitePeanoMesh a t N p

private theorem finitePeanoMesh_continuousOn {a : ℝ} (ha : 0 < a) (N : ℕ) (p : ℝ) :
    ContinuousOn (fun t => finitePeanoMesh a t N p) (Icc 0 1) := by
  unfold finitePeanoMesh
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro j _
  unfold peanoPower
  apply continuousOn_const.mul
  have hc : ContinuousOn (fun t : ℝ => a + t + (j : ℝ) * a) (Icc 0 1) := by fun_prop
  apply hc.rpow_const
  intro t ht
  exact Or.inl (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ha ht.1)
    (mul_nonneg (Nat.cast_nonneg j) ha.le)).ne'

theorem weightedFinitePeano_convex {a M : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 1)) (hW : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t)
    (hArea : (∫ t in (0 : ℝ)..1, w t) = 1 / 2) (N : ℕ)
    (hBad : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc (1 : ℝ) (9 / 5),
      a * ∑ j ∈ Finset.range N, peanoExponentBad p (a + t + j * a) ≤ M) :
    ConvexOn ℝ (Icc 1 (9 / 5)) (fun p => weightedFinitePeano a w N p + (M / 4) * p ^ 2) := by
  let F (p t : ℝ) := w t * (finitePeanoMesh a t N p + (M / 2) * p ^ 2)
  have hFC (p : ℝ) : ContinuousOn (F p) (Icc 0 1) :=
    hw.mul ((finitePeanoMesh_continuousOn ha N p).add continuousOn_const)
  have hI (p : ℝ) : IntervalIntegrable (F p) volume 0 1 :=
    (hFC p).intervalIntegrable_of_Icc zero_le_one
  have hEq (p : ℝ) : (∫ t in (0 : ℝ)..1, F p t) = weightedFinitePeano a w N p + (M / 4) * p ^ 2 := by
    let f (t : ℝ) := w t * finitePeanoMesh a t N p
    let g (t : ℝ) := w t * ((M / 2) * p ^ 2)
    have hf : IntervalIntegrable f volume 0 1 :=
      (hw.mul (finitePeanoMesh_continuousOn ha N p)).intervalIntegrable_of_Icc zero_le_one
    have hg : IntervalIntegrable g volume 0 1 := (hw.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
    have hE (t : ℝ) : F p t = f t + g t := by dsimp only [F, f, g]; ring
    simp_rw [hE]
    rw [intervalIntegral.integral_add hf hg, show (∫ t in (0 : ℝ)..1, f t) = weightedFinitePeano a w N p from rfl]
    dsimp only [g]
    rw [intervalIntegral.integral_mul_const, hArea]
    ring
  refine ⟨convex_Icc _ _, ?_⟩
  intro p hp q hq c d hc hd hcd
  simp only [smul_eq_mul]
  rw [← hEq, ← hEq, ← hEq, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add ((hI p).const_mul c) ((hI q).const_mul d)]
  apply intervalIntegral.integral_mono_on zero_le_one (hI (c * p + d * q))
    (((hI p).const_mul c).add ((hI q).const_mul d))
  intro t ht
  have hC := (finitePeanoMesh_convex ha ht.1 N (hBad t ht)).2 hp hq hc hd hcd
  simp only [smul_eq_mul] at hC
  have h := mul_le_mul_of_nonneg_left hC (hW t ht)
  dsimp only [F]
  exact h.trans_eq (by ring)

end ACS12.GammaMeasure
