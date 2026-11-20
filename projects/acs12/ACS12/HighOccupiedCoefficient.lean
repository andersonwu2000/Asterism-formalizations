import ACS12.HighMinimumReference

/-! The complete occupied-neighbor coefficient on the containing ray p ≥ 2. -/
namespace ACS12.Pressure

open Set
open GammaMeasure (log_three_tight)

noncomputable def occupiedCoefficient (ν : ℝ) : ℝ :=
  (ν - 1) * ν / (1 + ν ^ (1 / ν)) ^ ν

private theorem log_div_antitone_three :
    AntitoneOn (fun ν : ℝ => Real.log ν / ν) (Ici 3) := by
  have hD (ν : ℝ) (hν : 0 < ν) :
      HasDerivAt (fun x : ℝ => Real.log x / x) ((1 - Real.log ν) / ν ^ 2) ν := by
    convert (Real.hasDerivAt_log hν.ne').div (hasDerivAt_id ν) hν.ne' using 1
    simp only [id_eq]
    field_simp [hν.ne']
    <;> ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro ν hν
    exact (hD ν (by have h : 3 ≤ ν := hν; linarith only [h])).continuousAt.continuousWithinAt
  · intro ν hν
    exact (hD ν (by have h : 3 ≤ ν := interior_subset hν; linarith only [h])).differentiableAt.differentiableWithinAt
  · intro ν hν
    have hν₃ : 3 ≤ ν := interior_subset hν
    have hL : 1 ≤ Real.log ν := by
      have h₃ : 1 < Real.log 3 := by linarith only [log_three_tight.1]
      exact h₃.le.trans (Real.log_le_log (by norm_num) hν₃)
    rw [(hD ν (by linarith only [hν₃])).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hL) (sq_nonneg _)

private theorem occupied_log_deriv {ν : ℝ} (hν : 1 < ν) :
    HasDerivAt (fun x : ℝ => Real.log (occupiedCoefficient x))
      (1 / (ν - 1) + 1 / ν - Real.log (1 + ν ^ (1 / ν)) +
        (ν ^ (1 / ν) / (1 + ν ^ (1 / ν))) * (Real.log ν - 1) / ν) ν := by
  let v (x : ℝ) := Real.exp (Real.log x / x)
  let f (x : ℝ) := Real.log (x - 1) + Real.log x - x * Real.log (1 + v x)
  have hν₀ := zero_lt_one.trans hν
  have hV : 0 < v ν := Real.exp_pos _
  have hDlog : HasDerivAt (fun x : ℝ => Real.log x / x) ((1 - Real.log ν) / ν ^ 2) ν := by
    convert (Real.hasDerivAt_log hν₀.ne').div (hasDerivAt_id ν) hν₀.ne' using 1
    simp only [id_eq]
    field_simp [hν₀.ne']
    <;> ring
  have hDV := hDlog.exp
  have hDL := (hDV.const_add 1).log (show 1 + v ν ≠ 0 by positivity)
  have hDA := ((hasDerivAt_id ν).sub_const 1).log (sub_pos.mpr hν).ne'
  have hDF := (hDA.add (Real.hasDerivAt_log hν₀.ne')).sub ((hasDerivAt_id ν).mul hDL)
  have hEq : (fun x => Real.log (occupiedCoefficient x)) =ᶠ[nhds ν] f := by
    filter_upwards [Ioi_mem_nhds hν] with x hx
    have hx₁ : 1 < x := hx
    have hx₀ := zero_lt_one.trans hx₁
    have hR : x ^ (1 / x) = v x := by
      unfold v
      rw [Real.rpow_def_of_pos hx₀]
      congr 1
      ring
    unfold occupiedCoefficient f
    rw [Real.log_div (mul_pos (sub_pos.mpr hx₁) hx₀).ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.log_mul (sub_pos.mpr hx₁).ne' hx₀.ne',Real.log_rpow (by positivity : 0 < 1 + x ^ (1 / x)),hR]
  apply HasDerivAt.congr_of_eventuallyEq _ hEq
  convert hDF using 1
  simp only [id_eq,one_mul,hν₀.ne',v] at *
  rw [Real.rpow_def_of_pos hν₀]
  have hE : Real.exp (Real.log ν * (1 / ν)) = Real.exp (Real.log ν / ν) := by congr 1; ring
  rw [hE]
  field_simp [hν₀.ne',(sub_pos.mpr hν).ne',show 1 + Real.exp (Real.log ν / ν) ≠ 0 by positivity]
  <;> ring

theorem occupiedCoefficient_log_antitone :
    AntitoneOn (fun ν => Real.log (occupiedCoefficient ν)) (Ici 3) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro ν hν
    exact (occupied_log_deriv (by have h : 3 ≤ ν := hν; linarith only [h])).continuousAt.continuousWithinAt
  · intro ν hν
    have h₃ : 3 ≤ ν := interior_subset hν
    exact (occupied_log_deriv (by linarith only [h₃])).differentiableAt.differentiableWithinAt
  · intro ν hν
    have h₃ : 3 ≤ ν := interior_subset hν
    have hν₀ : 0 < ν := by linarith only [h₃]
    have hν₁ : 0 < ν - 1 := by linarith only [h₃]
    let v := ν ^ (1 / ν)
    have hv : 0 < v := Real.rpow_pos_of_pos hν₀ _
    have hLogν : 1 ≤ Real.log ν := by
      exact (show 1 ≤ Real.log 3 by linarith only [log_three_tight.1]).trans
        (Real.log_le_log (by norm_num) h₃)
    have hAMGM : Real.log 2 + Real.log ν / (2 * ν) ≤ Real.log (1 + v) := by
      have h := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 : ℝ) ∈ Ioi 0 by change (0 : ℝ) < 1; norm_num)
        hv (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      simp only [smul_eq_mul,Real.log_one,mul_zero,zero_add] at h
      have hArg : (1 / 2 : ℝ) * 1 + (1 / 2) * v = (1 + v) / 2 := by ring
      rw [hArg,Real.log_div (by positivity : 0 < 1 + v).ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
      have hLv : Real.log v = Real.log ν / ν := by
        unfold v
        rw [Real.log_rpow hν₀]
        ring
      rw [hLv] at h
      have hE : Real.log ν / (2 * ν) = (1 / 2) * (Real.log ν / ν) := by ring
      rw [hE]
      linarith only [h]
    have hFrac : v / (1 + v) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hv])
    have hProd := mul_le_mul_of_nonneg_right hFrac (div_nonneg (sub_nonneg.mpr hLogν) hν₀.le)
    have hInv : 1 / (ν - 1) ≤ (1 / 2 : ℝ) := (div_le_iff₀ hν₁).mpr (by linarith only [h₃])
    have hLog := log_div_antitone_three (show (3 : ℝ) ∈ Ici 3 by change (3 : ℝ) ≤ 3; exact le_rfl) h₃ h₃
    have hNum : (1 / 2 : ℝ) + Real.log 3 / 6 - Real.log 2 < 0 := by
      linarith only [log_three_tight.2,Real.log_two_gt_d9]
    rw [(occupied_log_deriv (by linarith only [h₃])).deriv]
    change 1 / (ν - 1) + 1 / ν - Real.log (1 + v) + v / (1 + v) * (Real.log ν - 1) / ν ≤ 0
    have hE : v / (1 + v) * (Real.log ν - 1) / ν = v / (1 + v) * ((Real.log ν - 1) / ν) := by ring
    rw [hE]
    have hI : 1 / ν + (Real.log ν - 1) / ν = Real.log ν / ν := by ring
    have hL : Real.log ν / (2 * ν) = (Real.log ν / ν) / 2 := by ring
    linarith only [hAMGM,hProd,hInv,hLog,hNum,hI,hL]

private theorem occupiedCoefficient_three_lt : occupiedCoefficient 3 < 5 / 12 := by
  let v := (3 : ℝ) ^ (1 / 3 : ℝ)
  have hv : 0 < v := Real.rpow_pos_of_pos (by norm_num) _
  have hV : v ^ 3 = 3 := by
    unfold v
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hLower : (10 / 7 : ℝ) < v := by
    by_contra! h
    have hP := pow_le_pow_left₀ hv.le h 3
    norm_num at hP
    linarith only [hP,hV]
  have hV₂ : (100 / 49 : ℝ) < v ^ 2 := by
    have h := pow_lt_pow_left₀ hLower (by norm_num : (0 : ℝ) ≤ 10 / 7) (by decide : 2 ≠ 0)
    norm_num at h
    exact h
  have hDen : (72 / 5 : ℝ) < (1 + v) ^ 3 := by nlinarith only [hV,hLower,hV₂]
  unfold occupiedCoefficient
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num,Real.rpow_ofNat]
  change 6 / (1 + v) ^ 3 < 5 / 12
  apply (div_lt_iff₀ (pow_pos (by positivity : 0 < 1 + v) 3)).mpr
  linarith only [hDen]

theorem occupiedCoefficient_lt {ν : ℝ} (hν : 3 ≤ ν) : occupiedCoefficient ν < 5 / 12 := by
  have hν₀ : 0 < ν := by linarith only [hν]
  have hPos : 0 < occupiedCoefficient ν := by
    unfold occupiedCoefficient
    exact div_pos (mul_pos (by linarith only [hν] : 0 < ν - 1) hν₀) (Real.rpow_pos_of_pos (by positivity) _)
  have hPos₃ : 0 < occupiedCoefficient 3 := by unfold occupiedCoefficient; positivity
  have h := occupiedCoefficient_log_antitone (show (3 : ℝ) ∈ Ici 3 by change (3 : ℝ) ≤ 3; exact le_rfl) hν hν
  exact ((Real.log_le_log_iff hPos hPos₃).mp h).trans_lt occupiedCoefficient_three_lt

end ACS12.Pressure
