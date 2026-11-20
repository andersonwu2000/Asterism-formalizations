import ACS12.FullBoseSine
import ACS12.GammaDeficitMomentReduction

/-! The ordinary beta sine identity enters the entire original Bose row by an absolutely integrable double integral. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter GammaMeasure GammaDeficit
open CenteredCircle.AllN

theorem ordinaryBeta_bose_sine {p N : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hN : 0 < N) :
    boseRow p N = (4*nativeGammaScale p/sineScale p) *
      ∫ v : ℝ in Ioi 0, sinhProfile p v *
        ∫ s : ℝ in Ioi 0, Real.sin (v*s)/(Real.exp ((2*Real.pi/N)*s)-1) := by
  let μ := volume.restrict (Ioi (0:ℝ))
  let d := 2*Real.pi/N
  let F (a : ℝ × ℝ) := sinhProfile p a.2 * (Real.sin (a.1*a.2)/(Real.exp (d*a.1)-1))
  let G (s : ℝ) := s/(Real.exp (d*s)-1)
  let H (v : ℝ) := v*sinhProfile p v
  have hd : 0 < d := by unfold d; positivity
  have hG : Integrable G μ := by
    apply Integrable.of_integral_ne_zero
    change (∫ s : ℝ in Ioi 0, s/(Real.exp (d*s)-1)) ≠ 0
    have h := completeBose_natMoment (r := 1) (by decide) hd
    norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,one_mul,one_add_one_eq_two] at h
    rw [h]
    exact (div_pos (powerTail_pos (by norm_num : (1:ℝ)<2) (by decide)) (pow_pos hd 2)).ne'
  have hH : Integrable H μ := sinhProfile_moment_one_integrable hp (by linarith : p<2)
  have hM : Measurable F := by unfold F sinhProfile; fun_prop
  have hS : ∀ᵐ a : ℝ × ℝ ∂μ.prod μ, 0 < a.1 ∧ 0 < a.2 :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi))
  have hFI : Integrable F (μ.prod μ) := by
    apply (hG.mul_prod hH).mono' hM.aestronglyMeasurable
    filter_upwards [hS] with a ha
    have hDen := expTail_den_pos (mul_pos hd ha.1)
    have hProfile : 0 ≤ sinhProfile p a.2 := by
      unfold sinhProfile
      exact Real.rpow_nonneg (mul_nonneg (by norm_num)
        (Real.sinh_pos_iff.mpr (half_pos ha.2)).le) _
    unfold F G H
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hProfile,abs_div,abs_of_pos hDen]
    have hSin := Real.abs_sin_le_abs (x := a.1*a.2)
    rw [abs_mul,abs_of_pos ha.1,abs_of_pos ha.2] at hSin
    have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hSin hDen.le) hProfile
    convert h using 1 <;> ring
  have hRow (s : ℝ) : (∫ v, F (s,v) ∂μ) =
      sineScale p*normalizedImage p s/(Real.exp (d*s)-1) := by
    have hE : (fun v => F (s,v)) =
        (fun v => (sinhProfile p v*Real.sin (s*v))/(Real.exp (d*s)-1)) := by
      funext v
      unfold F
      ring
    rw [hE,integral_div,sinhProfile_sine hp hp₁]
    rfl
  have hRaw (s : ℝ) :
      2*gammaDensity p s*(2*Real.sinh (Real.pi*s)/(Real.exp (2*Real.pi*s/N)-1)) =
        (4*nativeGammaScale p/sineScale p)*(∫ v, F (s,v) ∂μ) := by
    rw [hRow]
    unfold normalizedImage gammaDensity nativeGammaScale
    have hArg : 2*Real.pi*s/N = d*s := by unfold d; ring
    rw [hArg]
    field_simp [(sineScale_pos hp hp₁).ne',(Real.Gamma_pos_of_pos hp).ne',Real.pi_ne_zero]
    <;> ring
  have hCol (v : ℝ) : (∫ s, F (s,v) ∂μ) =
      sinhProfile p v * ∫ s : ℝ in Ioi 0, Real.sin (v*s)/(Real.exp (d*s)-1) := by
    dsimp only [F]
    rw [integral_const_mul]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    dsimp only
    rw [mul_comm s v]
  calc
    _ = (4*nativeGammaScale p/sineScale p)*(∫ s, ∫ v, F (s,v) ∂μ ∂μ) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => hRaw s)
    _ = (4*nativeGammaScale p/sineScale p)*(∫ v, ∫ s, F (s,v) ∂μ ∂μ) := by
      rw [integral_integral_swap hFI]
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      exact hCol v

end ACS12.NativeCells
