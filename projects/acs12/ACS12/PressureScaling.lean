import ACS12.PressureIncident

/-! Exact scaling comparison under the actual image law. -/
namespace ACS12.Pressure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaDeficit (lineDensity)
open GammaMeasure (imageDensity imageDensity_pos imageDensity_two imageDensity_div_lineDensity_strictMono
  lineDensity_pos imagePotential imagePotential_integrable imagePotential_pos imageSlope)

theorem imagePotential_scaled_upper {p L t u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 < t) (htu : t ≤ u) :
    imagePotential p L u ≤ (t / u) ^ p * imagePotential p L t := by
  let c := u / t
  have hp₀ := zero_lt_one.trans_le hp
  have hu := ht.trans_le htu
  have hc : 0 < c := div_pos hu ht
  have hc₁ : 1 ≤ c := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using htu)
  let f (s : ℝ) := imageDensity p L s * Real.exp (-s * t)
  let g (s : ℝ) := imageDensity p L (s / c) * Real.exp (-s * t)
  have hEq (s : ℝ) : g (s * c) = imageDensity p L s * Real.exp (-s * u) := by
    dsimp only [g]
    rw [mul_div_cancel_right₀ _ hc.ne']
    congr 2
    dsimp only [c]
    field_simp [ht.ne']
  have hf : IntegrableOn f (Ioi 0) := imagePotential_integrable hp₀ hL ht
  have hg : IntegrableOn g (Ioi 0) := by
    have h : IntegrableOn (fun s => g (s * c)) (Ioi 0) :=
      (imagePotential_integrable hp₀ hL hu).congr (Eventually.of_forall fun s => (hEq s).symm)
    simpa only [zero_mul] using (integrableOn_Ioi_comp_mul_right_iff g 0 hc).mp h
  have hRat : MonotoneOn (fun s => imageDensity p L s / lineDensity p s) (Ioi 0) := by
    rcases hp₂.eq_or_lt with rfl | hp₂'
    · intro s hs t ht h
      have h₂ (x : ℝ) : lineDensity 2 x = x := by norm_num [lineDensity,Real.Gamma_two]
      simp only [imageDensity_two hL hs,imageDensity_two hL ht,h₂,
        div_self (show 0 < s from hs).ne',div_self (show 0 < t from ht).ne',le_rfl]
    · exact (imageDensity_div_lineDensity_strictMono hp hp₂' hL).monotoneOn
  have hPoint (s : ℝ) (hs : 0 < s) : g s ≤ c ^ (1 - p) * f s := by
    have hS := div_pos hs hc
    have h := hRat (mem_Ioi.mpr hS) (mem_Ioi.mpr hs) (div_le_self hs.le hc₁)
    have hR : lineDensity p (s / c) = lineDensity p s * c ^ (1 - p) := by
      unfold lineDensity
      rw [Real.div_rpow hs.le hc.le,show 1 - p = -(p - 1) by ring,Real.rpow_neg hc.le]
      ring
    dsimp only at h
    have h' := (div_le_iff₀ (lineDensity_pos hp₀ hS)).mp h
    rw [hR,← mul_assoc,div_mul_cancel₀] at h'
    · simpa only [g,f,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_right h' (Real.exp_pos (-s * t)).le
    · exact (lineDensity_pos hp₀ hs).ne'
  have hCmp := setIntegral_mono_on hg (hf.const_mul (c ^ (1 - p))) measurableSet_Ioi hPoint
  rw [integral_const_mul] at hCmp
  have hI : imagePotential p L u = c⁻¹ * ∫ s : ℝ in Ioi 0, g s := by
    unfold imagePotential
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => (hEq s).symm),
      integral_comp_mul_right_Ioi g 0 hc,zero_mul,smul_eq_mul]
  have hF : c⁻¹ * c ^ (1 - p) = (t / u) ^ p := by
    rw [show t / u = c⁻¹ by unfold c; rw [inv_div],Real.inv_rpow hc.le,
      ← Real.rpow_neg hc.le,← Real.rpow_neg_one,← Real.rpow_add hc]
    congr 1
    ring
  rw [hI,← hF,mul_assoc]
  exact mul_le_mul_of_nonneg_left hCmp (inv_nonneg.mpr hc.le)

theorem pressure_unit_normalized_gt {n : ℕ} {p : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    {Q : ℝ} (hQ : 1 ≤ Q) :
    let S := C.source
    (7 / 5 : ℝ) * (Q * imagePotential p S.period Q) < pressureAt p S S.root := by
  let S := C.source
  let L := S.period
  let b := S.mass S.neighbor
  let k := imagePotential p L
  have hp₁ : 1 ≤ p := by linarith only [hp]
  have hp₀ := zero_lt_one.trans_le hp₁
  have hQ₀ := zero_lt_one.trans_le hQ
  have hK₁ : 0 < k 1 := imagePotential_pos hp₀ S.period_pos zero_lt_one
  have hB := incident_neighbor_gt_five_sevenths ((by norm_num : (3 / 2 : ℝ) ≤ 9 / 5).trans hp) hp₂ F C
  change 5 / 7 < b at hB
  have hU := (imageSlope_elasticity hp₁ hp₂ S.period_pos).1
  have hPi := pressure_unit_gt hp₀ hp₂ F C
  change b * imageSlope p L 1 * (1 + b / 8) < pressureAt p S S.root at hPi
  have hK := imagePotential_scaled_upper hp₁ hp₂ S.period_pos zero_lt_one hQ
  change k Q ≤ (1 / Q) ^ p * k 1 at hK
  rw [one_div, Real.inv_rpow hQ₀.le, ← Real.rpow_neg hQ₀.le] at hK
  have hR : Q * Q ^ (-p) ≤ 1 := by
    rw [mul_comm,← Real.rpow_add_one hQ₀.ne']
    exact (Real.rpow_le_rpow_of_exponent_le hQ (show -p + 1 ≤ 0 by linarith only [hp₁])).trans_eq
      (Real.rpow_zero Q)
  have hK' : Q * k Q ≤ k 1 := by
    calc
      _ ≤ Q * (Q ^ (-p) * k 1) := mul_le_mul_of_nonneg_left hK hQ₀.le
      _ = (Q * Q ^ (-p)) * k 1 := by ring
      _ ≤ k 1 := mul_le_of_le_one_left hK₁.le hR
  have hBu : 0 < b := S.mass_pos _
  have hB' : 305 / 392 < b * (1 + b / 8) := by
    have h := mul_pos (sub_pos.mpr hB) (show 0 < 1 + (b + 5 / 7) / 8 by positivity)
    nlinarith only [h]
  have hC : 7 / 5 ≤ p * (b * (1 + b / 8)) := by
    calc
      _ ≤ (9 / 5) * (305 / 392) := by norm_num
      _ ≤ p * (b * (1 + b / 8)) := mul_le_mul hp hB'.le (by norm_num) hp₀.le
  calc
    _ ≤ (7 / 5) * k 1 := mul_le_mul_of_nonneg_left hK' (by norm_num)
    _ ≤ p * (b * (1 + b / 8)) * k 1 := mul_le_mul_of_nonneg_right hC hK₁.le
    _ ≤ b * imageSlope p L 1 * (1 + b / 8) := by
      have h := mul_le_mul_of_nonneg_left hU (show 0 ≤ b * (1 + b / 8) by positivity)
      linarith only [h]
    _ < _ := hPi

end ACS12.Pressure
