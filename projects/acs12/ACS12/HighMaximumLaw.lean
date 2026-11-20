import ACS12.GammaLogCurvature
import ACS12.GammaEulerLaw

/-! The full two-to-four Gamma comparison with the elementary maximum-fee density. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def maximumLawScale (L : ℝ) : ℝ := (2 * Real.pi / L) ^ 2

theorem maximumLawScale_pos {L : ℝ} (hL : 0 < L) : 0 < maximumLawScale L := by
  unfold maximumLawScale
  positivity

private theorem contrast_log_differences {q x y : ℝ} (hq : 0 < q) :
    gammaLogContrast q x y = Real.log ‖Complex.Gamma (gammaArgument q y)‖ -
      Real.log ‖Complex.Gamma (gammaArgument q x)‖ := by
  unfold gammaLogContrast
  rw [Real.log_div (norm_gamma_argument_ne hq y) (norm_gamma_argument_ne hq x)]

theorem maximumLaw_imageRatio_mono {p L : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) (hL : 0 < L) :
    MonotoneOn (fun s : ℝ => imageDensity p L s / (s * (s ^ 2 + maximumLawScale L) ^ ((p - 2) / 2))) (Ioi 0) := by
  let q := p / 2
  let θ := (p - 2) / 2
  let c := maximumLawScale L
  let D (s : ℝ) := s ^ 2 + c
  let t (s : ℝ) := L * s / (2 * Real.pi)
  let k (s : ℝ) := imageDensity p L s / s
  let G (a s : ℝ) := ‖Complex.Gamma (gammaArgument a (t s))‖
  let C := (Real.pi / L) ^ (p - 1) * (2 : ℝ) ^ (p - 1) /
    (Real.Gamma p * (Real.pi / L) * 2)
  have hp₀ : 0 < p := by linarith only [hp]
  have hq : 0 < q := by unfold q; positivity
  have hc := maximumLawScale_pos hL
  have hD (s : ℝ) : 0 < D s := add_pos_of_nonneg_of_pos (sq_nonneg s) hc
  have hC : 0 < C := by unfold C; positivity
  have hθ₀ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have hθ₁ : 0 ≤ 1 - θ := by unfold θ; linarith only [hP]
  have hG (a s : ℝ) (ha : 0 < a) : G a s ≠ 0 := norm_gamma_argument_ne ha _
  have hK (s : ℝ) (hs : 0 < s) : Real.log (k s) = Real.log C + 2 * (Real.log (G q s) - Real.log (G 1 s)) := by
    unfold k
    rw [imageDensity_div_eq_ratio hp₀ hL hs]
    change Real.log (C * (G q s / G 1 s) ^ 2) = _
    rw [Real.log_mul hC.ne' (pow_ne_zero _ (div_ne_zero (hG q s hq) (hG 1 s zero_lt_one))),
      Real.log_pow,Real.log_div (hG q s hq) (hG 1 s zero_lt_one)]
    norm_num
  have hEndpoint (s : ℝ) : 2 * (Real.log (G 2 s) - Real.log (G 1 s)) =
      Real.log (D s) - Real.log c := by
    let z := gammaArgument 1 (t s)
    have hz : z ≠ 0 := by
      intro h
      have hRe := congrArg Complex.re h
      simp [z] at hRe
    have he : gammaArgument 2 (t s) = z + 1 := by
      unfold z gammaArgument
      norm_num
      ring
    have hRec : G 2 s = ‖z‖ * G 1 s := by
      unfold G
      rw [he,Complex.Gamma_add_one z hz,norm_mul]
    have hzD : ‖z‖ ^ 2 = D s / c := by
      have h := norm_gammaArgument_add 1 (t s) 0
      norm_num at h
      change ‖z‖ ^ 2 = _ at h
      rw [h]
      unfold D c maximumLawScale t
      field_simp [hL.ne',Real.pi_ne_zero] <;> ring
    rw [hRec,Real.log_mul (norm_ne_zero_iff.mpr hz) (hG 1 s zero_lt_one)]
    rw [show 2 * (Real.log ‖z‖ + Real.log (G 1 s) - Real.log (G 1 s)) = 2 * Real.log ‖z‖ by ring,
      ← show Real.log (‖z‖ ^ (2 : ℕ)) = 2 * Real.log ‖z‖ by norm_num [Real.log_pow],hzD,
      Real.log_div (hD s).ne' hc.ne']
  intro x hx y hy hxy
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have ht₀ : 0 ≤ t x := by unfold t; positivity
  have htxy : t x ≤ t y := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hL.le) (by positivity)
  have hJ := (gammaLogContrast_concave_all ht₀ htxy).2
    (show (1 : ℝ) ∈ Ici (1 / 2) by norm_num) (show (2 : ℝ) ∈ Ici (1 / 2) by norm_num)
    hθ₁ hθ₀ (sub_add_cancel 1 θ)
  simp only [smul_eq_mul] at hJ
  rw [show (1 - θ) * 1 + θ * 2 = q by unfold θ q; ring] at hJ
  rw [contrast_log_differences hq,contrast_log_differences zero_lt_one,contrast_log_differences (by norm_num : (0 : ℝ) < 2)] at hJ
  change (1 - θ) * (Real.log (G 1 y) - Real.log (G 1 x)) + θ * (Real.log (G 2 y) - Real.log (G 2 x)) ≤
    Real.log (G q y) - Real.log (G q x) at hJ
  have hW (s : ℝ) (hs : 0 < s) : 0 < k s := div_pos (imageDensity_pos hp₀ hL hs) hs
  have hLog (s : ℝ) (hs : 0 < s) : Real.log (k s / D s ^ θ) = Real.log (k s) - θ * Real.log (D s) := by
    rw [Real.log_div (hW s hs).ne' (Real.rpow_pos_of_pos (hD s) θ).ne',Real.log_rpow (hD s)]
  change imageDensity p L x / (x * D x ^ θ) ≤ imageDensity p L y / (y * D y ^ θ)
  rw [← div_div,← div_div]
  change k x / D x ^ θ ≤ k y / D y ^ θ
  apply (Real.log_le_log_iff (div_pos (hW x hx₀) (Real.rpow_pos_of_pos (hD x) θ))
    (div_pos (hW y hy₀) (Real.rpow_pos_of_pos (hD y) θ))).mp
  rw [hLog x hx₀,hLog y hy₀,hK x hx₀,hK y hy₀]
  have hX := congrArg (θ * ·) (hEndpoint x)
  have hY := congrArg (θ * ·) (hEndpoint y)
  nlinarith only [hJ,hX,hY]

end ACS12.GammaMeasure
