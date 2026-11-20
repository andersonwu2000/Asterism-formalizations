import ACS12.GammaLogCurvature
import ACS12.GammaRadialComparison

/-! Ordering of the exact Gamma density relative to its pure power. -/

namespace ACS12.GammaMeasure

open Set
open GammaDeficit (lineDensity)

private noncomputable def densityRatio (q x : ℝ) : ℝ :=
  Real.sinh (Real.pi * x) * ‖Complex.Gamma (gammaArgument q x)‖ ^ 2 /
    (Real.pi * x ^ (2 * q - 1))

private theorem gammaArgument_Gamma_pos {q : ℝ} (hq : 0 < q) (x : ℝ) :
    0 < ‖Complex.Gamma (gammaArgument q x)‖ :=
  norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hq))

private theorem densityRatio_pos {q x : ℝ} (hq : 0 < q) (hx : 0 < x) : 0 < densityRatio q x := by
  unfold densityRatio
  exact div_pos
    (mul_pos (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx))
      (sq_pos_of_pos (gammaArgument_Gamma_pos hq x)))
    (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx _))

private theorem imageDensity_div_lineDensity {p L s : ℝ} (hp : 0 < p) (hL : 0 < L) (hs : 0 < s) :
    imageDensity p L s / lineDensity p s = densityRatio (p / 2) (L * s / (2 * Real.pi)) := by
  let η := 2 * Real.pi / L
  let x := L * s / (2 * Real.pi)
  have hη : 0 < η := by dsimp [η]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hηx : η * x = s := by dsimp [η, x]; field_simp [hL.ne', Real.pi_ne_zero]
  have hPower : (Real.pi / L) ^ (p - 1) * (2 : ℝ) ^ (p - 1) * x ^ (p - 1) = s ^ (p - 1) := by
    rw [← Real.mul_rpow (div_nonneg Real.pi_pos.le hL.le) (by norm_num),
      show Real.pi / L * 2 = η by dsimp [η]; ring,
      ← Real.mul_rpow hη.le hx.le, hηx]
  have hπx : Real.pi * x = L * s / 2 := by dsimp [x]; field_simp [Real.pi_ne_zero]
  rw [imageDensity_eq_spectral p hL, gammaDensity, densityRatio, lineDensity, gammaArgument]
  change ((Real.pi / L) ^ (p - 1) *
    ((2 : ℝ) ^ (p - 1) * ‖Complex.Gamma ((p / 2 : ℝ) + (x : ℂ) * Complex.I)‖ ^ 2 /
      (Real.pi * Real.Gamma p)) * Real.sinh (L * s / 2)) /
    (s ^ (p - 1) / Real.Gamma p) =
    Real.sinh (Real.pi * x) * ‖Complex.Gamma ((p / 2 : ℝ) + (x : ℂ) * Complex.I)‖ ^ 2 /
      (Real.pi * x ^ (2 * (p / 2) - 1))
  rw [hπx, show 2 * (p / 2) - 1 = p - 1 by ring, ← hPower]
  field_simp [Real.pi_ne_zero, (Real.Gamma_pos_of_pos hp).ne',
    (Real.rpow_pos_of_pos hx (p - 1)).ne', (Real.rpow_pos_of_pos hη (p - 1)).ne',
    (Real.rpow_pos_of_pos (div_pos Real.pi_pos hL) (p - 1)).ne']
 
private theorem densityRatio_half {x : ℝ} (hx : 0 < x) :
    densityRatio (1 / 2) x = Real.tanh (Real.pi * x) := by
  have hP : 0 < 2 * Real.pi := by positivity
  have hx' : 2 * Real.pi * x / (2 * Real.pi) = x := by field_simp [Real.pi_ne_zero]
  have h := imageDensity_div_lineDensity (p := 1) zero_lt_one hP hx
  rw [hx', imageDensity_one, lineDensity, sub_self, Real.rpow_zero, Real.Gamma_one, div_one] at h
  rw [← h, div_one, show 2 * Real.pi * x / 2 = Real.pi * x by ring]

private theorem densityRatio_one {x : ℝ} (hx : 0 < x) : densityRatio 1 x = 1 := by
  have hP : 0 < 2 * Real.pi := by positivity
  have hx' : 2 * Real.pi * x / (2 * Real.pi) = x := by field_simp [Real.pi_ne_zero]
  have h := imageDensity_div_lineDensity (p := 2) (by norm_num) hP hx
  rw [hx', imageDensity_two hP hx, lineDensity] at h
  norm_num at h
  exact h.symm.trans (div_self hx.ne')

private theorem log_densityRatio {q x : ℝ} (hq : 0 < q) (hx : 0 < x) :
    Real.log (densityRatio q x) =
      Real.log (Real.sinh (Real.pi * x)) +
        2 * Real.log ‖Complex.Gamma (gammaArgument q x)‖ -
        (Real.log Real.pi + (2 * q - 1) * Real.log x) := by
  have hs := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx)
  have hG := gammaArgument_Gamma_pos hq x
  unfold densityRatio
  rw [Real.log_div (mul_pos hs (sq_pos_of_pos hG)).ne'
      (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hx _)).ne',
    Real.log_mul hs.ne' (sq_pos_of_pos hG).ne',
    Real.log_mul Real.pi_ne_zero (Real.rpow_pos_of_pos hx _).ne',
    Real.log_pow, Real.log_rpow hx]
  norm_num

private theorem log_densityRatio_sub {q x y : ℝ} (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) :
    Real.log (densityRatio q y) - Real.log (densityRatio q x) =
      2 * gammaLogContrast q x y +
        (Real.log (Real.sinh (Real.pi * y)) - Real.log (Real.sinh (Real.pi * x))) -
        (2 * q - 1) * (Real.log y - Real.log x) := by
  rw [log_densityRatio hq hx, log_densityRatio hq hy, gammaLogContrast,
    Real.log_div (gammaArgument_Gamma_pos hq y).ne' (gammaArgument_Gamma_pos hq x).ne']
  ring

private theorem tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  have ha := Real.exp_lt_exp.mpr hxy
  have hb := Real.exp_lt_exp.mpr (neg_lt_neg hxy)
  have h := mul_lt_mul ha hb.le (Real.exp_pos (-y)) (Real.exp_pos y).le
  rw [Real.tanh_eq, Real.tanh_eq]
  exact (div_lt_div_iff₀ (by positivity) (by positivity)).mpr (by linarith only [h])

private theorem densityRatio_strictMono {q : ℝ} (hq : 1 / 2 ≤ q) (hq₁ : q < 1) :
    StrictMonoOn (densityRatio q) (Ioi 0) := by
  intro x hx y hy hxy
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have hq₀ : 0 < q := by linarith
  let a := 2 * (1 - q)
  let b := 2 * q - 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hEq : a * (1 / 2) + b * 1 = q := by dsimp [a, b]; ring
  have hG := (gammaLogContrast_concave hx₀.le hxy.le).2 (by norm_num : (1 / 2 : ℝ) ∈ Icc (1 / 2) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (1 / 2) 1) ha.le hb hab
  simp only [smul_eq_mul, hEq] at hG
  have hX := log_densityRatio_sub (q := q) hq₀ hx₀ hy₀
  have hA := log_densityRatio_sub (q := 1 / 2) (by norm_num) hx₀ hy₀
  have hB := log_densityRatio_sub (q := 1) zero_lt_one hx₀ hy₀
  rw [densityRatio_half hx₀, densityRatio_half hy₀] at hA
  rw [densityRatio_one hx₀, densityRatio_one hy₀, sub_self] at hB
  have hT : Real.log (Real.tanh (Real.pi * x)) < Real.log (Real.tanh (Real.pi * y)) := by
    have hxT := densityRatio_pos (q := 1 / 2) (by norm_num) hx₀
    rw [densityRatio_half hx₀] at hxT
    exact Real.log_lt_log hxT (tanh_strictMono (mul_lt_mul_of_pos_left hxy Real.pi_pos))
  apply (Real.log_lt_log_iff (densityRatio_pos hq₀ hx₀) (densityRatio_pos hq₀ hy₀)).mp
  have hLower := mul_pos ha (sub_pos.mpr hT)
  dsimp only [a, b] at hG hLower
  nlinarith only [hG, hX, hA, hB, hLower,
    congrArg (fun r : ℝ => a * r) hA, congrArg (fun r : ℝ => b * r) hB]

theorem imageDensity_div_lineDensity_strictMono {p L : ℝ} (hp : 1 ≤ p) (hp₂ : p < 2)
    (hL : 0 < L) : StrictMonoOn (fun s => imageDensity p L s / lineDensity p s) (Ioi 0) := by
  intro x hx y hy hxy
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  dsimp only
  rw [imageDensity_div_lineDensity hp₀ hL hx₀, imageDensity_div_lineDensity hp₀ hL hy₀]
  exact densityRatio_strictMono (by linarith : 1 / 2 ≤ p / 2) (by linarith)
    (show 0 < L * x / (2 * Real.pi) by positivity)
    (show 0 < L * y / (2 * Real.pi) by positivity)
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hxy hL) (by positivity))


theorem imageDensity_div_lineDensity_strictAnti {p L : ℝ} (hp : 2 < p) (hL : 0 < L) :
    StrictAntiOn (fun s => imageDensity p L s / lineDensity p s) (Ioi 0) := by
  let q := p / 2
  have hq : 1 < q := by unfold q; linarith only [hp]
  have hp₀ : 0 < p := by linarith only [hp]
  have hAnti : StrictAntiOn (densityRatio q) (Ioi 0) := by
    intro x hx y hy hxy
    have hx₀ : 0 < x := hx
    have hy₀ : 0 < y := hy
    let a := (q - 1) / (q - 1 / 2)
    let b := (1 / 2) / (q - 1 / 2)
    have hDen : 0 < q - 1 / 2 := by linarith only [hq]
    have ha : 0 < a := div_pos (sub_pos.mpr hq) hDen
    have hb : 0 < b := div_pos (by norm_num) hDen
    have hab : a + b = 1 := by
      unfold a b
      rw [← add_div]
      have hE : q - 1 + 1 / 2 = q - 1 / 2 := by ring
      rw [hE,div_self hDen.ne']
    have hEq : a * (1 / 2) + b * q = 1 := by
      unfold a b
      calc
        _ = (((q - 1) * (1 / 2)) + (1 / 2) * q) / (q - 1 / 2) := by ring
        _ = _ := (div_eq_iff hDen.ne').mpr (by ring)
    have hG := (gammaLogContrast_concave_all hx₀.le hxy.le).2
      (by norm_num : (1 / 2 : ℝ) ∈ Ici (1 / 2))
      (show q ∈ Ici (1 / 2) from by change 1 / 2 ≤ q; linarith only [hq]) ha.le hb.le hab
    simp only [smul_eq_mul,hEq] at hG
    have hX := log_densityRatio_sub (q := q) (zero_lt_one.trans hq) hx₀ hy₀
    have hA := log_densityRatio_sub (q := 1 / 2) (by norm_num) hx₀ hy₀
    have hB := log_densityRatio_sub (q := 1) zero_lt_one hx₀ hy₀
    rw [densityRatio_half hx₀,densityRatio_half hy₀] at hA
    rw [densityRatio_one hx₀,densityRatio_one hy₀,sub_self] at hB
    have hxT := densityRatio_pos (q := 1 / 2) (by norm_num) hx₀
    rw [densityRatio_half hx₀] at hxT
    have hT := Real.log_lt_log hxT (tanh_strictMono (mul_lt_mul_of_pos_left hxy Real.pi_pos))
    have hPos := mul_pos ha (sub_pos.mpr hT)
    have hSum := congrArg (fun r : ℝ => r * (Real.log (Real.sinh (Real.pi * y)) -
      Real.log (Real.sinh (Real.pi * x)))) hab
    have hScale : a * (2 * (1 / 2 : ℝ) - 1) + b * (2 * q - 1) = 1 := by
      linarith only [hEq,hab]
    have hCoef := congrArg (fun r : ℝ => r * (Real.log y - Real.log x)) hScale
    apply (Real.log_lt_log_iff (densityRatio_pos (zero_lt_one.trans hq) hy₀)
      (densityRatio_pos (zero_lt_one.trans hq) hx₀)).mp
    by_contra! h
    have hNonneg := mul_nonneg hb.le (sub_nonneg.mpr h)
    have hAA := congrArg (fun r : ℝ => a * r) hA
    have hXX := congrArg (fun r : ℝ => b * r) hX
    dsimp only at hSum hCoef hAA hXX
    nlinarith only [hG,hB,hPos,hNonneg,hSum,hCoef,hAA,hXX]
  intro x hx y hy hxy
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  dsimp only
  rw [imageDensity_div_lineDensity hp₀ hL hy₀,imageDensity_div_lineDensity hp₀ hL hx₀]
  exact hAnti (show 0 < L * x / (2 * Real.pi) by positivity)
    (show 0 < L * y / (2 * Real.pi) by positivity)
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hxy hL) (by positivity))

end ACS12.GammaMeasure
