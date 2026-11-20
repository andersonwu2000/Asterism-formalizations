import ACS12.PureZCurvature
import ACS12.PowerLogMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The lower and upper complete exponent curvature bounds W21. -/
namespace ACS12.GammaMeasure

open Filter Set
open scoped Topology

theorem logPower_decay {q : ℝ} (hq : 0 < q) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ (-q) * Real.log x ^ k) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hq).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.rpow_natCast,Real.rpow_neg (zero_le_one.trans hx),div_eq_mul_inv,mul_comm]

theorem pureZ_second_bounds {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    37 / 500 < p * powerLogTail (p + 1) 2 1 - 2 * powerLogTail (p + 1) 1 1 ∧
    p * powerLogTail (p + 1) 2 1 - 2 * powerLogTail (p + 1) 1 1 ≤ 1 / 8 := by
  let f := zetaCurvature p
  let F := zetaCurvaturePrimitive p
  let b (N : ℕ) : ℝ := 4 + ((N + 1 : ℕ) : ℝ)
  let v := p * powerLogTail (p + 1) 2 1 - 2 * powerLogTail (p + 1) 1 1
  have hp₀ := zero_lt_one.trans_le hp
  have hq : 1 < p + 1 := by linarith only [hp]
  have hT : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (N + 5), f (1 + j)) atTop (𝓝 v) := by
    have hA := ((powerLogTail_summable hq 2 1 le_rfl).hasSum.mul_left p).sub
      ((powerLogTail_summable hq 1 1 le_rfl).hasSum.mul_left 2)
    have hE (j : ℕ) : p * (((1 : ℕ) : ℝ) + j) ^ (-(p + 1)) * Real.log (((1 : ℕ) : ℝ) + j) ^ 2 -
        2 * (((1 : ℕ) : ℝ) + j) ^ (-(p + 1)) * Real.log (((1 : ℕ) : ℝ) + j) =
        f (1 + j) := by
      simp only [Nat.cast_one,f,zetaCurvature]
      ring
    have hF : HasSum (fun j : ℕ => f (1 + j)) v := by
      convert hA using 1
      funext j
      dsimp only [Pi.sub_apply]
      linear_combination -(hE j)
    exact hF.tendsto_sum_nat.comp (tendsto_add_atTop_nat 5)
  have hbT : Tendsto b atTop atTop := by
    apply tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ))
    · intro N
      dsimp only [b]
      push_cast
      linarith
    · exact tendsto_natCast_atTop_atTop
  have hF : Tendsto F atTop (𝓝 0) := by
    simpa only [F,zetaCurvaturePrimitive,neg_zero] using (logPower_decay hp₀ 2).neg
  have hf : Tendsto f atTop (𝓝 0) := by
    have h := ((logPower_decay (show 0 < p + 1 by positivity) 2).const_mul p).sub
      ((logPower_decay (show 0 < p + 1 by positivity) 1).const_mul 2)
    simp only [mul_zero,sub_zero] at h
    apply h.congr'
    filter_upwards [] with x
    simp only [f,zetaCurvature,pow_one]
    ring
  have hBoundary : Tendsto (fun N => (299 / 4000 : ℝ) + F (b N) + f (b N) / 2) atTop
      (𝓝 (299 / 4000)) := by
    simpa only [add_zero,zero_div] using ((hF.comp hbT).const_add (299 / 4000)).add ((hf.comp hbT).div_const 2)
  have hL := le_of_tendsto_of_tendsto hBoundary hT
    (Eventually.of_forall fun N => (zetaCurvature_partial_bounds hp hP N).2.le)
  have hU := le_of_tendsto_of_tendsto hT tendsto_const_nhds
    (Eventually.of_forall fun N => (zetaCurvature_partial_bounds hp hP N).1.le)
  exact ⟨(by norm_num : (37 / 500 : ℝ) < 299 / 4000).trans_le hL,hU⟩

end ACS12.GammaMeasure
