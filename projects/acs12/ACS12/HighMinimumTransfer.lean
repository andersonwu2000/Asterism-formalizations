import ACS12.PressureMinimumTransfer
import ACS12.GammaSourceElasticity

/-! The unchanged fixed-neighbor minimum test under its actual high Gamma law. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure
open GammaDeficit (lineDensity)

private theorem highMinimumTest_integrable {d : ℝ → ℝ} {a r g Z : ℝ} (ha : 0 ≤ a) (hr : 0 < r) (hg : r ≤ g)
    (hd : ∀ s > 0, 0 ≤ d s) (hM : Measurable d)
    (hI : IntegrableOn d (Ioi 0)) (hS : IntegrableOn (fun s => d s * s) (Ioi 0)) :
    IntegrableOn (fun s => d s * (minimumAtomTest a r g s - Z)) (Ioi 0) := by
  have hF : Measurable (minimumAtomTest a r g) := by
    unfold minimumAtomTest oppositeRayBose pressureBose periodicDen
    fun_prop
  apply ((hS.const_mul a).add (hI.const_mul (1 + |Z|))).mono'
    (hM.mul (hF.sub_const Z)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  obtain ⟨hF₀,hF₁⟩ := minimumAtomTest_bounds ha hr hg hs
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hd s hs)]
  have hAbs : |minimumAtomTest a r g s - Z| ≤ a * s + 1 + |Z| := by
    have h := abs_add_le (minimumAtomTest a r g s) (-Z)
    rw [abs_neg,abs_of_nonneg hF₀,← sub_eq_add_neg] at h
    exact h.trans (add_le_add_left hF₁ _)
  have h := mul_le_mul_of_nonneg_left hAbs (hd s hs)
  simp only [Pi.add_apply]
  linarith only [h]

theorem highMinimumAtom_actual_le {p L a r g t t₀ Z : ℝ}
    (hp : 2 ≤ p) (hL : 0 < L) (ha : 0 ≤ a) (hr : 0 < r) (hg : r ≤ g)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (hZ : 1 ≤ Z)
    (hRef : (∫ s : ℝ in Ioi 0, lineDensity p s * Real.exp (-s * t₀) * (minimumAtomTest a r g s - Z)) ≤ 0) :
    (∫ s : ℝ in Ioi 0, imageDensity p L s * Real.exp (-s * t) * minimumAtomTest a r g s) ≤
      Z * imagePotential p L t := by
  let b (s : ℝ) := imageDensity p L s * Real.exp (-s * t)
  let c (s : ℝ) := lineDensity p s * Real.exp (-s * t₀)
  let W (s : ℝ) := c s * s
  let Q (s : ℝ) := (minimumAtomTest a r g s - Z) / s
  let R (s : ℝ) := (imageDensity p L s / lineDensity p s) * Real.exp (-s * (t - t₀))
  have hp₀ : 0 < p := by linarith only [hp]
  have ht' := ht₀.trans_le ht
  have hMb : Measurable b := (continuous_imageDensity hp₀ hL).measurable.mul (by fun_prop)
  have hMc : Measurable c := by unfold c lineDensity; fun_prop
  have hPb (s : ℝ) (hs : 0 < s) : 0 < b s := mul_pos (imageDensity_pos hp₀ hL hs) (Real.exp_pos _)
  have hPc (s : ℝ) (hs : 0 < s) : 0 < c s := mul_pos (lineDensity_pos hp₀ hs) (Real.exp_pos _)
  have hbI : IntegrableOn b (Ioi 0) := imagePotential_integrable hp₀ hL ht'
  have hcI : IntegrableOn c (Ioi 0) := by
    simpa only [c,mul_one] using GammaDeficit.lineDensity_exp_integrable hp₀ ht₀
  have hBI : IntegrableOn (fun s => b s * s) (Ioi 0) := by
    simpa only [b,mul_right_comm] using imageSlope_integrable hp₀ hL ht'
  have hWI : IntegrableOn W (Ioi 0) := by simpa only [W,c,pow_one,mul_right_comm] using (lineDensity_moment hp₀ ht₀ 1).1
  have hTb := highMinimumTest_integrable (Z := Z) ha hr hg (fun s hs => (hPb s hs).le) hMb hbI hBI
  have hTc := highMinimumTest_integrable (Z := Z) ha hr hg (fun s hs => (hPc s hs).le) hMc hcI hWI
  have hWR (s : ℝ) (hs : 0 < s) : W s * R s = b s * s := by
    have hExp : Real.exp (-s * t₀) * Real.exp (-s * (t - t₀)) = Real.exp (-s * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hρ : lineDensity p s * (imageDensity p L s / lineDensity p s) = imageDensity p L s := by
      field_simp [(lineDensity_pos hp₀ hs).ne']
    calc
      _ = (lineDensity p s * (imageDensity p L s / lineDensity p s)) * s *
        (Real.exp (-s * t₀) * Real.exp (-s * (t - t₀))) := by unfold W R c; ring
      _ = _ := by rw [hρ,hExp]; unfold b; ring
  have hWQ (s : ℝ) (hs : 0 < s) : W s * Q s = c s * (minimumAtomTest a r g s - Z) := by
    unfold W Q
    field_simp [hs.ne']
  have hProd (s : ℝ) (hs : 0 < s) : W s * Q s * R s = b s * (minimumAtomTest a r g s - Z) := by
    rw [mul_right_comm,hWR s hs]
    unfold Q
    field_simp [hs.ne']
  have hQ : IntegrableOn (fun s => W s * Q s) (Ioi 0) := hTc.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hWQ s hs).symm)
  have hR : IntegrableOn (fun s => W s * R s) (Ioi 0) := hBI.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hWR s hs).symm)
  have hP : IntegrableOn (fun s => W s * Q s * R s) (Ioi 0) := hTb.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hProd s hs).symm)
  have hRatio : AntitoneOn R (Ioi 0) := by
    intro x hx y hy hxy
    have hE := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hxy)] :
      -y * (t - t₀) ≤ -x * (t - t₀))
    exact mul_le_mul (imageDensity_div_lineDensity_antitone hp hL hx hy hxy) hE
      (Real.exp_pos _).le (div_pos (imageDensity_pos hp₀ hL hx) (lineDensity_pos hp₀ hx)).le
  have hRef' : (∫ s : ℝ in Ioi 0, W s * Q s) ≤ 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hWQ s hs)]
    exact hRef
  have h := integral_antitone_product_nonpos hWI hQ hR hP
    (fun s hs => mul_pos (hPc s hs) hs)
    (fun s hs => mul_nonneg (div_pos (imageDensity_pos hp₀ hL hs) (lineDensity_pos hp₀ hs)).le (Real.exp_pos _).le)
    (minimumAtomTest_div_mono hr hg hZ) hRatio hRef'
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hProd s hs)] at h
  have hI : IntegrableOn (fun s => b s * minimumAtomTest a r g s) (Ioi 0) :=
    (hTb.add (hbI.const_mul Z)).congr (Eventually.of_forall fun s => by simp only [Pi.add_apply]; ring)
  have hE : (∫ s : ℝ in Ioi 0, b s * (minimumAtomTest a r g s - Z)) =
      (∫ s : ℝ in Ioi 0, b s * minimumAtomTest a r g s) - Z * imagePotential p L t := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => b s * minimumAtomTest a r g s - Z * b s)
      (fun s _ => by ring),integral_sub hI (hbI.const_mul Z),integral_const_mul]
    rfl
  rwa [hE,sub_nonpos] at h

end ACS12.Pressure
