import ACS12.HighSwitchReceiver
import ACS12.HighPressureRange
import ACS12.HighMinimumSource

/-! The full original-source mass floor on 2 ≤ p ≤ 4. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN
open GammaMeasure

private theorem highSelfCoefficient_le {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) :
    highSelfCoefficient p / 2 ≤ 29 / 24 := by
  unfold highSelfCoefficient
  have h₂ : p ^ 2 ≤ 16 := by
    have h := mul_nonneg (show 0 ≤ p by linarith only [hp]) (sub_nonneg.mpr hP)
    nlinarith only [h,hP]
  linarith only [h₂,hP]

theorem high_original_mass_floor {n : ℕ} {p : ℝ} (hn : 4 ≤ n) (hp : 2 ≤ p) (hP : p ≤ 4)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) (i j : Fin n) :
    2 * C.source.mass j / (7 * p) < C.source.mass i := by
  let S := C.source
  let L := S.period
  let k := imagePotential p L
  let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
  let self := imageSelf p L
  have hp₀ : 0 < p := by linarith only [hp]
  obtain ⟨imax,_,hMax⟩ := Finset.univ.exists_max_image S.mass
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨i,Finset.mem_univ _⟩)
  obtain ⟨imin,_,hMin⟩ := Finset.univ.exists_min_image S.mass
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨i,Finset.mem_univ _⟩)
  let Q := S.mass imax
  let a := S.mass imin
  let D := Q * k Q
  let R := (c + Q * self) / D
  let P := pressureAt p S imin
  have hQ := S.mass_pos imax
  have ha := S.mass_pos imin
  have hD : 0 < D := mul_pos hQ (imagePotential_pos hp₀ S.period_pos hQ)
  have hSelf : 0 < self := imageSelf_pos hp₀ S.period_pos
  have hQ₁ : 1 ≤ Q := by rw [← S.mass_root]; exact hMax _ (Finset.mem_univ _)
  obtain ⟨hC,hR,hRU⟩ := high_original_pressure_range (by omega) hp F C imax (fun z => hMax z (Finset.mem_univ _))
  change D < c at hC
  change 1 < R at hR
  change R < 33 / 10 at hRU
  have hUnit := high_pressure_unit_normalized_gt hp hP F C hQ₁
  rw [pressure_constant_all hp₀ F C S.root imin] at hUnit
  change highUnitCoefficient p * D < P at hUnit
  have hUnitAffine := mul_le_mul_of_nonneg_right (highUnitCoefficient_ge_affine hp hP) hD.le
  have hUnit' : highUnitAffine p < P / D := (lt_div_iff₀ hD).mpr (hUnitAffine.trans_lt hUnit)
  have hMaxP := high_pressure_maximum_normalized_gt hn hp hP F C imax (fun z => hMax z (Finset.mem_univ _))
  change R - (11 - p) / 10 < pressureAt p C.source imax / D at hMaxP
  rw [pressure_constant_all hp₀ F C imax imin] at hMaxP
  change R - (11 - p) / 10 < P / D at hMaxP
  have hA : 2 * Q / (7 * p) < a := by
    by_contra! hBad
    have hSeven : 0 < 7 * p := by positivity
    have haQ : a / Q ≤ 2 / (7 * p) := by
      apply (div_le_iff₀ hQ).mpr
      have hEq : 2 * Q / (7 * p) = (2 / (7 * p)) * Q := by ring
      rwa [← hEq]
    have haQ₇ : a ≤ Q / 7 := by
      have hFrac : 2 / (7 * p) ≤ (1 / 7 : ℝ) := (div_le_iff₀ hSeven).mpr (by linarith only [hp])
      have h := haQ.trans hFrac
      have h' := (div_le_iff₀ hQ).mp h
      linarith only [h']
    have hSmall : 2 * a < Q := by linarith only [haQ₇,hQ]
    have hc : 0 < c := hD.trans hC
    obtain ⟨t,ht,hT⟩ := high_exists_imagePotential_eq hp S.period_pos (div_pos hc (by positivity : 0 < 2 * a))
    let x := c / D
    have hx : 0 < x := div_pos hc hD
    have hxR : x ≤ R := by
      unfold x R
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hQ.le hSelf.le)) hD.le
    have hX : c = x * (Q * k Q) := by unfold x D; rw [div_mul_cancel₀ _ hD.ne']
    have hY := high_inverseMinimum_square hp S.period_pos ha hQ ht hSmall hC hT hX
    have hY₂ : (a / t) ^ 2 ≤ R / (7 * p) := by
      have h := mul_le_mul haQ hxR hx.le (show 0 ≤ 2 / (7 * p) by positivity)
      have h' := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
      have hEq : ((2 / (7 * p)) * R) / 2 = R / (7 * p) := by ring
      rw [hEq] at h'
      exact hY.trans h'
    let y := Real.sqrt (R / (7 * p))
    have hy : 0 ≤ y := Real.sqrt_nonneg _
    have hy₂ : y ^ 2 = R / (7 * p) := Real.sq_sqrt (by positivity)
    have hY' : a / t ≤ y := by
      have hya : 0 ≤ a / t := div_nonneg ha.le ht.le
      nlinarith only [hY₂,hy₂,hy,hya]
    let V := max 1 (highMinimumUnitPrice p y)
    have hV : 1 ≤ V := le_max_left _ _
    have hCap : max 1 (highMinimumUnitPrice p (a / t)) ≤ V :=
      max_le_max le_rfl (highMinimumUnitPrice_mono hp (div_nonneg ha.le ht.le) hy hY')
    have hMinP := high_original_minimum_pressure_le (by omega) hp F C imin
      (fun z => hMin z (Finset.mem_univ _)) ht hT
    change P ≤ c / 2 * max 1 (highMinimumUnitPrice p (a / t)) +
      (highSelfCoefficient p / 2) * a * self at hMinP
    have hSelfCap := highSelfCoefficient_le hp hP
    have hSelfNonneg : 0 ≤ highSelfCoefficient p / 2 := by unfold highSelfCoefficient; positivity
    have hPaySelf : (highSelfCoefficient p / 2) * a ≤ Q * V / 2 := by
      have h := mul_le_mul_of_nonneg_right hSelfCap ha.le
      have h' := mul_le_mul_of_nonneg_left haQ₇ (by norm_num : (0 : ℝ) ≤ 29 / 24)
      have h'' := mul_le_mul_of_nonneg_left hV hQ.le
      change (highSelfCoefficient p / 2) * a ≤ (29 / 24) * a at h
      change Q * 1 ≤ Q * V at h''
      have hQpos : 0 < Q := hQ
      linarith only [h,h',h'',hQpos]
    have hPay : P / D ≤ highPressureEnvelope p R := by
      have hB := mul_le_mul_of_nonneg_left hCap (show 0 ≤ c / 2 by positivity)
      have hS := mul_le_mul_of_nonneg_right hPaySelf hSelf.le
      have hRD : R * D = c + Q * self := div_mul_cancel₀ _ hD.ne'
      apply (div_le_iff₀ hD).mpr
      change P ≤ (R / 2 * V) * D
      nlinarith only [hMinP,hB,hS,congrArg (fun z : ℝ => z * V / 2) hRD]
    have hReceiver := highPressureEnvelope_lt_lower hp hP hR.le hRU.le
    have hLower : max (highUnitAffine p) (R - (11 - p) / 10) < P / D := max_lt hUnit' hMaxP
    exact (hReceiver.trans hLower).not_ge hPay
  have hJ : 2 * S.mass j / (7 * p) ≤ 2 * Q / (7 * p) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hMax j (Finset.mem_univ _)) (by norm_num)) (by positivity)
  exact hJ.trans_lt (hA.trans_le (hMin i (Finset.mem_univ _)))

end ACS12.Pressure
