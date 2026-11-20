import ACS12.PressureBose
import ACS12.PressureCutMeasure

/-! The strict original maximum pressure lower, including all self and image terms. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity imageDensity_pos imagePotential imageSelf imageTailIntegrand
  imageTailIntegrand_integrable imageTail_integral)

theorem ray_radial_integral {n : ℕ} {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (m d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    IntegrableOn (fun s => imageDensity p L s * rayWeight L m d s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, imageDensity p L s * rayWeight L m d s) =
        ∑ i, m i * imageTail (imagePotential p L) L (d i) := by
  let f (i : Fin n) (s : ℝ) := m i * imageTailIntegrand p L (d i) s
  have hI (i : Fin n) : IntegrableOn (f i) (Ioi 0) :=
    (imageTailIntegrand_integrable hp hL (hd i)).const_mul (m i)
  have hEq (s : ℝ) : imageDensity p L s * rayWeight L m d s = ∑ i, f i s := by
    dsimp only [rayWeight,periodicDen,imageTailIntegrand,f]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  constructor
  · exact (integrable_finsetSum _ (fun i _ => hI i)).congr (Eventually.of_forall fun s => (hEq s).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),integral_finsetSum _ (fun i _ => hI i)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [integral_const_mul,← imageTail_integral hp hL (hd i)]

noncomputable def maximumDebit (p L Q : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0, pressureWeight p L s * pressureBose Q s ^ 2

theorem maximumDebit_integrable {p L Q : ℝ} (hp : 0 < p)
    (hL : 0 < L) (hQ : 0 < Q) :
    IntegrableOn (fun s => pressureWeight p L s * pressureBose Q s ^ 2) (Ioi 0) := by
  apply ((stressKernel_integrable_all hp hL hQ (show 0 < 2 * Q by positivity)).const_mul (Q ^ 2)).congr
  exact Eventually.of_forall fun s => by
    dsimp only [pressureWeight,pressureBose]
    rw [show -s * (2 * Q) = -s * Q + -s * Q by ring,Real.exp_add]
    ring

private theorem rayWeight_pos {n : ℕ} {L s : ℝ} (i : Fin n) (hL : 0 < L) (hs : 0 < s)
    (m d : Fin n → ℝ) (hm : ∀ j, 0 < m j) : 0 < rayWeight L m d s := by
  unfold rayWeight
  exact Finset.sum_pos (fun j _ => mul_pos (hm j) (div_pos (Real.exp_pos _) (periodicDen_pos hL hs)))
    ⟨i,Finset.mem_univ _⟩

theorem pressure_maximum_gt {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (hp : 0 < p)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (hCaps : C.source.HasCircularMassCaps) (i : Fin n) (hMax : ∀ j, C.source.mass j ≤ C.source.mass i) :
    let S := C.source
    let Q := S.mass i
    F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) + Q * imageSelf p S.period -
      maximumDebit p S.period Q < pressureAt p S i := by
  let S := C.source
  let L := S.period
  let Q := S.mass i
  let A := leftRay S i
  let B := rightRay S i
  let W := pressureWeight p L
  let f (s : ℝ) := W s * ((A s + Q) * B s)
  let g (s : ℝ) := W s * (A s * (B s + Q))
  let H (s : ℝ) := W s * (A s * B s + (Q / 2) * (A s + B s))
  let k (s : ℝ) := imageDensity p L s * (A s + B s)
  let d (s : ℝ) := W s * pressureBose Q s ^ 2
  have hL := S.period_pos
  have hQ := S.mass_pos i
  have hA := ray_integrable hp hL S.mass _ (fun j => S.forwardDistance_pos j i)
  have hB := ray_integrable hp hL S.mass _ (S.forwardDistance_pos i)
  have hAB := rays_product_integrable_all hp hL S.mass _ _ (fun j => S.forwardDistance_pos j i)
    (S.forwardDistance_pos i)
  change IntegrableOn (fun s => W s * A s) (Ioi 0) at hA
  change IntegrableOn (fun s => W s * B s) (Ioi 0) at hB
  change IntegrableOn (fun s => W s * (A s * B s)) (Ioi 0) at hAB
  have hf : IntegrableOn f (Ioi 0) := (hAB.add (hB.const_mul Q)).congr
    (Eventually.of_forall fun s => by dsimp only [f,Pi.add_apply]; ring)
  have hg : IntegrableOn g (Ioi 0) := (hAB.add (hA.const_mul Q)).congr
    (Eventually.of_forall fun s => by dsimp only [g,Pi.add_apply]; ring)
  have hAvg (s : ℝ) : H s = (f s + g s) / 2 := by dsimp only [H,f,g]; ring
  have hH : IntegrableOn H (Ioi 0) := ((hf.add hg).div_const 2).congr
    (Eventually.of_forall fun s => (hAvg s).symm)
  have hPi : (∫ s : ℝ in Ioi 0, H s) = pressureAt p S i := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hAvg s),integral_div,integral_add hf hg]
    change (pressureAt p S i + pressureBefore p S i) / 2 = _
    rw [← pressureThroughSite_all hp F C i]
    ring
  obtain ⟨hAr,hArE⟩ := ray_radial_integral hp hL S.mass _ (fun j => S.forwardDistance_pos j i)
  obtain ⟨hBr,hBrE⟩ := ray_radial_integral hp hL S.mass _ (S.forwardDistance_pos i)
  change IntegrableOn (fun s => imageDensity p L s * A s) (Ioi 0) at hAr
  change IntegrableOn (fun s => imageDensity p L s * B s) (Ioi 0) at hBr
  have hEq (s : ℝ) : k s = imageDensity p L s * A s + imageDensity p L s * B s := by
    dsimp only [k]; ring
  have hk : IntegrableOn k (Ioi 0) := (hAr.add hBr).congr (Eventually.of_forall fun s => (hEq s).symm)
  have hRad : (∫ s : ℝ in Ioi 0, k s) =
      F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) + Q * imageSelf p L := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),integral_add hAr hBr]
    dsimp only [A,B,leftRay,rightRay]
    rw [hArE,hBrE,add_comm]
    exact F.chart_radial_images C hp i
  have hd : IntegrableOn d (Ioi 0) := maximumDebit_integrable hp hL hQ
  have hPoint (s : ℝ) (hs : 0 < s) : k s - d s < H s := by
    obtain ⟨hA',hB'⟩ := maximum_rays_le hn S hCaps i hMax hs
    have hA₀ := rayWeight_pos i hL hs S.mass (fun j => S.forwardDistance j i) S.mass_pos
    have hB₀ := rayWeight_pos i hL hs S.mass (S.forwardDistance i) S.mass_pos
    change 0 < A s at hA₀
    change 0 < B s at hB₀
    have h := mul_lt_mul_of_pos_left (pressureBose_product_gt hQ hs hA₀ hB₀ hA' hB')
      (imageDensity_pos hp hL hs)
    dsimp only [k,d,H,W,pressureWeight]
    linarith only [h]
  let μ := volume.restrict (Ioi (0 : ℝ))
  let e (s : ℝ) := H s - (k s - d s)
  have he : Integrable e μ := hH.sub (hk.sub hd)
  have he₀ : ∀ᵐ s ∂μ, 0 ≤ e s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (sub_pos.mpr (hPoint s hs)).le
  have hSupp : Ioi (0 : ℝ) ⊆ Function.support e := fun s hs => (sub_pos.mpr (hPoint s hs)).ne'
  have hSuppPos : 0 < μ (Function.support e) := by
    apply lt_of_lt_of_le _ (measure_mono hSupp)
    rw [Measure.restrict_apply measurableSet_Ioi,inter_self]
    apply lt_of_lt_of_le _ (measure_mono (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1))
    rw [Real.volume_Ioo]
    norm_num
  have hInt := (integral_pos_iff_support_of_nonneg_ae he₀ he).mpr hSuppPos
  change 0 < ∫ s : ℝ in Ioi 0, H s - (k - d) s at hInt
  rw [integral_sub hH (hk.sub hd)] at hInt
  change 0 < (∫ s : ℝ in Ioi 0, H s) - ∫ s : ℝ in Ioi 0, k s - d s at hInt
  rw [integral_sub hk hd,hPi,hRad] at hInt
  exact sub_pos.mp hInt

end ACS12.Pressure
