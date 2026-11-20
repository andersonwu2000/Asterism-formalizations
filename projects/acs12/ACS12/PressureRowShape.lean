import ACS12.PressureActualRow
import ACS12.NativeLiteralRows

/-! Whole real-count order and strict log-count concavity of the actual row. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaDeficit (signedDensity)
open GammaMeasure (signedDensity_pos)
open NativeCells (analyticRow_pos analyticRow_two_eq)

theorem pressureLogCountRow_pos {p v : ℝ} (hp : 0 < p) (hv : 0 < v) :
    0 < pressureLogCountRow p v := by
  unfold pressureLogCountRow
  exact mul_pos (Real.exp_pos _) (analyticRow_pos hp (Real.one_lt_exp_iff.mpr hv))

private theorem pressureLogCountRow_two {v : ℝ} (hv : 0 < v) :
    pressureLogCountRow 2 v = (1 - Real.exp (-2 * v)) / 3 := by
  unfold pressureLogCountRow
  rw [analyticRow_two_eq (Real.one_lt_exp_iff.mpr hv)]
  have h : Real.exp (-2 * v) * Real.exp v ^ 2 = 1 := by
    rw [pow_two,← Real.exp_add,← Real.exp_add,show -2 * v + (v + v) = 0 by ring,Real.exp_zero]
  linear_combination h / 3

theorem pressureLogCountRow_shape {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) :
    StrictConcaveOn ℝ (Ioi 0) (pressureLogCountRow p) ∧
      StrictMonoOn (pressureLogCountRow p) (Ioi 0) := by
  rcases hp₂.eq_or_lt with rfl | hp₂'
  · constructor
    · refine ⟨convex_Ioi _,?_⟩
      intro x hx y hy hxy a b ha hb hab
      have hXY := (convex_Ioi (0 : ℝ)) hx hy ha.le hb.le hab
      have h₁ : 0 < x := hx
      have h₂ : 0 < y := hy
      have h₃ : 0 < a * x + b * y := hXY
      simp only [smul_eq_mul,pressureLogCountRow_two h₁,pressureLogCountRow_two h₂,pressureLogCountRow_two h₃]
      have hne : -2 * x ≠ -2 * y := fun h => hxy (by linarith only [h])
      have h := strictConvexOn_exp.2 (mem_univ (-2 * x)) (mem_univ (-2 * y)) hne ha hb hab
      simp only [smul_eq_mul] at h
      rw [show a * (-2 * x) + b * (-2 * y) = -2 * (a * x + b * y) by ring] at h
      linarith only [h,hab]
    · intro x hx y hy h
      rw [pressureLogCountRow_two hx,pressureLogCountRow_two hy]
      have hE := Real.exp_lt_exp.mpr (show -2 * y < -2 * x by linarith only [h])
      linarith only [hE]
  · let e := signedDensity p 1
    let G (v s : ℝ) := e s * calibratedBose p s v
    let C := 2 / Real.pi ^ p
    have hC : 0 < C := div_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _)
    have hI (v : ℝ) (hv : 0 < v) : IntegrableOn (G v) (Ioi 0) := (actualRow_calibrated hp hp₂' hv).1
    have hE (v : ℝ) (hv : 0 < v) : pressureLogCountRow p v = C *
        (GammaMeasure.powerTail p 1 - ∫ s : ℝ in Ioi 0, G v s) := (actualRow_calibrated hp hp₂' hv).2
    constructor
    · refine ⟨convex_Ioi _,?_⟩
      intro x hx y hy hxy a b ha hb hab
      have hXY : 0 < a * x + b * y := (convex_Ioi (0 : ℝ)) hx hy ha.le hb.le hab
      have hA : IntegrableOn (fun s => a * G x s + b * G y s) (Ioi 0) :=
        ((hI x hx).const_mul a).add ((hI y hy).const_mul b)
      have hB (s : ℝ) (hs : 0 < s) : G (a * x + b * y) s < a * G x s + b * G y s := by
        have h := (calibratedBose_strictConvex (p := p) hp.le hs).2
          (mem_univ x) (mem_univ y) hxy ha hb hab
        simp only [smul_eq_mul] at h
        have hP := mul_lt_mul_of_pos_left h (signedDensity_pos hp.le hp₂' zero_lt_one hs)
        dsimp only [G]
        linarith only [hP]
      let μ := volume.restrict (Ioi (0 : ℝ))
      letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
      have h := integral_strict_of_ae_lt μ (hI _ hXY) hA (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact hB s hs)
      rw [integral_add ((hI x hx).const_mul a) ((hI y hy).const_mul b),integral_const_mul,integral_const_mul] at h
      simp only [smul_eq_mul,hE x hx,hE y hy,hE _ hXY]
      have hP := mul_lt_mul_of_pos_left h hC
      nlinarith only [hP,congrArg (fun z : ℝ => z * C * GammaMeasure.powerTail p 1) hab]
    · intro x hx y hy hxy
      rw [hE x hx,hE y hy]
      let μ := volume.restrict (Ioi (0 : ℝ))
      letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
      have h := integral_strict_of_ae_lt μ (hI y hy) (hI x hx) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact mul_lt_mul_of_pos_left (calibratedBose_strictAnti hp.le hs hxy)
          (signedDensity_pos hp.le hp₂' zero_lt_one hs))
      exact mul_lt_mul_of_pos_left (sub_lt_sub_left h _) hC

theorem pressureLogCount_log_strictConcave {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) :
    StrictConcaveOn ℝ (Ioi 0) (fun v => Real.log (pressureLogCountRow p v)) := by
  obtain ⟨hC,hM⟩ := pressureLogCountRow_shape hp hp₂
  have hp₀ := zero_lt_one.trans hp
  let F := pressureLogCountRow p
  refine ⟨convex_Ioi _,?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hFx := pressureLogCountRow_pos hp₀ hx
  have hFy := pressureLogCountRow_pos hp₀ hy
  have hDiff : F x ≠ F y := hM.injOn.ne hx hy hxy
  have hA := strictConcaveOn_log_Ioi.2 (mem_Ioi.mpr hFx) (mem_Ioi.mpr hFy) hDiff ha hb hab
  have hB := hC.concaveOn.2 hx hy ha.le hb.le hab
  have hP : 0 < a * F x + b * F y := add_pos (mul_pos ha hFx) (mul_pos hb hFy)
  simp only [smul_eq_mul] at hA hB ⊢
  exact hA.trans_le (Real.log_le_log hP hB)

end ACS12.Pressure
