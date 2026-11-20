import ACS12.HighMinimumTransfer

/-! A complete high Gamma mean for the fixed original opposite neighbor. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure
open GammaDeficit (lineDensity lineDensity_exp_integrable lineDensity_exp_integral)

theorem pressureBose_midpoint {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    s * pressureBose r s ≤ Real.exp (-(r * s) / 2) := by
  let u := r * s
  have hu : 0 < u := mul_pos hr hs
  have hSinh := Real.self_le_sinh_iff.mpr (show 0 ≤ u / 2 by positivity)
  rw [Real.sinh_eq] at hSinh
  have hE₁ : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hE₂ : Real.exp (-(u / 2)) * Real.exp (-(u / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hS := mul_le_mul_of_nonneg_right hSinh (Real.exp_pos (-(u / 2))).le
  have hClear : u * Real.exp (-(u / 2)) ≤ 1 - Real.exp (-u) := by
    nlinarith only [hS,hE₁,hE₂]
  have hT := mul_le_mul_of_nonneg_right hClear (Real.exp_pos (-(u / 2))).le
  have hDen : 0 < 1 - Real.exp (-u) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu))
  unfold pressureBose periodicDen
  rw [show -s * r = -u by unfold u; ring]
  change s * (r * (Real.exp (-u) / (1 - Real.exp (-u)))) ≤ Real.exp (-u / 2)
  have hNum : s * (r * (Real.exp (-u) / (1 - Real.exp (-u)))) =
      u * Real.exp (-u) / (1 - Real.exp (-u)) := by
    calc
      _ = (r * s) * Real.exp (-u) / (1 - Real.exp (-u)) := by ring
      _ = _ := rfl
  rw [hNum]
  apply (div_le_iff₀ hDen).mpr
  rw [show -u / 2 = -(u / 2) by ring,← hE₂]
  rw [← hE₂] at hT
  nlinarith only [hT]

theorem minimumAtom_midpoint_bound {a r g s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    minimumAtomTest a r g s ≤ a * s + r * s * Real.exp (-g * s) + Real.exp (-(g + r / 2) * s) := by
  have hOpp : oppositeRayBose r g s = Real.exp (-g * s) * (r + pressureBose r s) := by
    have hE : Real.exp (-(g - r) * s) * Real.exp (-s * r) = Real.exp (-g * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hForm : oppositeRayBose r g s = r * Real.exp (-g * s) / periodicDen r s := by
      unfold oppositeRayBose pressureBose
      calc
        _ = r * (Real.exp (-(g - r) * s) * Real.exp (-s * r)) / periodicDen r s := by ring
        _ = _ := by rw [hE]
    have hD : 1 - Real.exp (-s * r) ≠ 0 := (periodicDen_pos hr hs).ne'
    have hId : (1 - Real.exp (-s * r))⁻¹ = 1 + Real.exp (-s * r) / (1 - Real.exp (-s * r)) := by
      apply (mul_right_cancel₀ hD)
      rw [inv_mul_cancel₀ hD,add_mul,one_mul,div_mul_cancel₀ _ hD]
      ring
    rw [hForm]
    unfold pressureBose periodicDen
    rw [div_eq_mul_inv, hId]
    ring
  have h := mul_le_mul_of_nonneg_left (pressureBose_midpoint hr hs) (Real.exp_pos (-g * s)).le
  have hE : Real.exp (-g * s) * Real.exp (-(r * s) / 2) = Real.exp (-(g + r / 2) * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hE] at h
  unfold minimumAtomTest
  rw [hOpp]
  nlinarith only [h]

noncomputable def highMinimumNeighborPrice (p a r g t : ℝ) : ℝ :=
  p * a / t + p * r * t ^ p * (t + g) ^ (-(p + 1)) +
    t ^ p * (t + g + r / 2) ^ (-p)

theorem high_minimumAtom_reference_le {p a r g t : ℝ} (hp : 0 < p)
    (ha : 0 ≤ a) (hr : 0 < r) (hg : r ≤ g) (ht : 0 < t) :
    let Z := max 1 (highMinimumNeighborPrice p a r g t)
    (∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s * t) * (minimumAtomTest a r g s - Z)) ≤ 0 := by
  let Z := max 1 (highMinimumNeighborPrice p a r g t)
  let w (s : ℝ) := lineDensity p s * Real.exp (-s * t)
  let f (s : ℝ) := w s * minimumAtomTest a r g s
  let A (s : ℝ) := a * (lineDensity p s * s * Real.exp (-s * t))
  let B (s : ℝ) := r * (lineDensity p s * s * Real.exp (-s * (t + g)))
  let C (s : ℝ) := lineDensity p s * Real.exp (-s * (t + g + r / 2))
  have hT : 0 < t + g := add_pos ht (hr.trans_le hg)
  have hT' : 0 < t + g + r / 2 := by positivity
  have hG : Real.Gamma (p + 1) / Real.Gamma p = p := by
    rw [Real.Gamma_add_one hp.ne']
    field_simp [(Real.Gamma_pos_of_pos hp).ne']
  have hw : IntegrableOn w (Ioi 0) := lineDensity_exp_integrable hp ht
  have hwS : IntegrableOn (fun s => w s * s) (Ioi 0) := by
    simpa only [w,pow_one,mul_right_comm] using (lineDensity_moment hp ht 1).1
  have hf : IntegrableOn f (Ioi 0) := by
    have hM : Measurable f := by unfold f w lineDensity minimumAtomTest oppositeRayBose pressureBose periodicDen; fun_prop
    apply ((hwS.const_mul a).add hw).mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have hw₀ : 0 ≤ w s := mul_nonneg (lineDensity_pos hp hs₀).le (Real.exp_pos _).le
    obtain ⟨h0,h1⟩ := minimumAtomTest_bounds ha hr hg hs₀
    rw [Real.norm_of_nonneg (mul_nonneg hw₀ h0)]
    have h := mul_le_mul_of_nonneg_left h1 hw₀
    simp only [f,Pi.add_apply]
    linarith only [h]
  have hA : IntegrableOn A (Ioi 0) := by simpa only [A,pow_one] using (lineDensity_moment hp ht 1).1.const_mul a
  have hB : IntegrableOn B (Ioi 0) := by simpa only [B,pow_one] using (lineDensity_moment hp hT 1).1.const_mul r
  have hC : IntegrableOn C (Ioi 0) := lineDensity_exp_integrable hp hT'
  have hCmp := integral_mono_ae hf ((hA.add hB).add hC) ?_
  · have hAE : (∫ s : ℝ in Ioi 0, A s) = a * p * t ^ (-(p + 1)) := by
      unfold A
      rw [integral_const_mul]
      have h := (lineDensity_moment hp ht 1).2
      simp only [Nat.cast_one,pow_one,hG] at h
      rw [h,mul_assoc]
    have hBE : (∫ s : ℝ in Ioi 0, B s) = r * p * (t + g) ^ (-(p + 1)) := by
      unfold B
      rw [integral_const_mul]
      have h := (lineDensity_moment hp hT 1).2
      simp only [Nat.cast_one,pow_one,hG] at h
      rw [h,mul_assoc]
    have hCE : (∫ s : ℝ in Ioi 0, C s) = (t + g + r / 2) ^ (-p) := lineDensity_exp_integral hp hT'
    simp only [Pi.add_apply] at hCmp
    rw [integral_add (f := fun s => A s + B s) (g := C) (hA.add hB) hC,integral_add hA hB,hAE,hBE,hCE] at hCmp
    have hPrice : a * p * t ^ (-(p + 1)) + r * p * (t + g) ^ (-(p + 1)) +
        (t + g + r / 2) ^ (-p) = highMinimumNeighborPrice p a r g t * t ^ (-p) := by
      have hInv : t ^ p * t ^ (-p) = 1 := by rw [← Real.rpow_add ht,add_neg_cancel,Real.rpow_zero]
      have hPow : t ^ (-(p + 1)) = t ^ (-p) / t := by
        rw [← Real.rpow_sub_one ht.ne',show -p - 1 = -(p + 1) by ring]
      unfold highMinimumNeighborPrice
      rw [hPow]
      linear_combination -(p * r * (t + g) ^ (-(p + 1)) + (t + g + r / 2) ^ (-p)) * hInv
    rw [hPrice] at hCmp
    have hZ : highMinimumNeighborPrice p a r g t * t ^ (-p) ≤ Z * t ^ (-p) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
    have hInt : (∫ s : ℝ in Ioi 0, w s * (minimumAtomTest a r g s - Z)) =
        (∫ s : ℝ in Ioi 0, f s) - Z * t ^ (-p) := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => f s - Z * w s)
        (fun s _ => by unfold f; ring),integral_sub hf (hw.const_mul Z),integral_const_mul]
      rw [show (∫ s : ℝ in Ioi 0, w s) = t ^ (-p) from lineDensity_exp_integral hp ht]
    change (∫ s : ℝ in Ioi 0, w s * (minimumAtomTest a r g s - Z)) ≤ 0
    rw [hInt]
    linarith only [hCmp,hZ]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs₀ : 0 < s := hs
    have h := mul_le_mul_of_nonneg_left (minimumAtom_midpoint_bound (a := a) (g := g) hr hs₀)
      (mul_nonneg (lineDensity_pos hp hs₀).le (Real.exp_pos (-s * t)).le)
    have hE₁ : Real.exp (-s * t) * Real.exp (-g * s) = Real.exp (-s * (t + g)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hE₂ : Real.exp (-s * t) * Real.exp (-(g + r / 2) * s) = Real.exp (-s * (t + g + r / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hEq : w s * (a * s + r * s * Real.exp (-g * s) + Real.exp (-(g + r / 2) * s)) =
        A s + B s + C s := by
      unfold w A B C
      calc
        _ = a * (lineDensity p s * s * Real.exp (-s * t)) +
            r * (lineDensity p s * s * (Real.exp (-s * t) * Real.exp (-g * s))) +
            lineDensity p s * (Real.exp (-s * t) * Real.exp (-(g + r / 2) * s)) := by ring
        _ = _ := by rw [hE₁,hE₂]
    change f s ≤ A s + B s + C s
    exact h.trans_eq hEq

end ACS12.Pressure
