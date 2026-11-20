import ACS12.PressureMaximum

/-! The original unit torque and its complete incident pressure lower. -/
namespace ACS12.Pressure

open Set Filter MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageSlope imageSlope_integrable imageSlopeTail_integrable imageSlope_samples_hasSum
  imageDensity_pos imageDensity_div_antitone)

theorem imageSlope_scaled_lower {p L t u : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ht : 0 < t) (htu : t ≤ u) :
    (t / u) ^ 3 * imageSlope p L t ≤ imageSlope p L u := by
  let c := u / t
  have hu := ht.trans_le htu
  have hc : 0 < c := div_pos hu ht
  have hc₁ : 1 ≤ c := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using htu)
  let f (s : ℝ) := GammaMeasure.imageDensity p L s * s * Real.exp (-s * t)
  let g (s : ℝ) := GammaMeasure.imageDensity p L (s / c) * (s / c) * Real.exp (-s * t)
  have hEq (s : ℝ) : g (s * c) = GammaMeasure.imageDensity p L s * s * Real.exp (-s * u) := by
    dsimp only [g]
    rw [mul_div_cancel_right₀ _ hc.ne']
    have h : - (s * c) * t = -s * u := by dsimp only [c]; field_simp [ht.ne']
    rw [h]
  have hf : IntegrableOn f (Ioi 0) := imageSlope_integrable hp hL ht
  have hg : IntegrableOn g (Ioi 0) := by
    have h : IntegrableOn (fun s => g (s * c)) (Ioi 0) :=
      (imageSlope_integrable hp hL hu).congr (Eventually.of_forall fun s => (hEq s).symm)
    simpa only [zero_mul] using (integrableOn_Ioi_comp_mul_right_iff g 0 hc).mp h
  have hPoint (s : ℝ) (hs : 0 < s) : c⁻¹ ^ 2 * f s ≤ g s := by
    have hd := div_pos hs hc
    have hLe := div_le_self hs.le hc₁
    have h := imageDensity_div_antitone hp hp₂ hL hd hs hLe
    have hW : GammaMeasure.imageDensity p L s * c⁻¹ ≤ GammaMeasure.imageDensity p L (s / c) := by
      have h' := (le_div_iff₀ hd).mp h
      have hE : GammaMeasure.imageDensity p L s / s * (s / c) =
          GammaMeasure.imageDensity p L s * c⁻¹ := by field_simp [hs.ne',hc.ne']
      rwa [hE] at h'
    have hS := mul_le_mul_of_nonneg_right hW (show 0 ≤ (s / c) * Real.exp (-s * t) by positivity)
    calc
      _ = GammaMeasure.imageDensity p L s * c⁻¹ * (s / c * Real.exp (-s * t)) := by
        dsimp only [f]
        rw [div_eq_mul_inv]
        ring
      _ ≤ _ := hS.trans_eq (by dsimp only [g]; ring)
  have hC := setIntegral_mono_on (hf.const_mul (c⁻¹ ^ 2)) hg measurableSet_Ioi hPoint
  rw [integral_const_mul] at hC
  have hI : imageSlope p L u = c⁻¹ * ∫ s : ℝ in Ioi 0, g s := by
    unfold imageSlope
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => (hEq s).symm),
      integral_comp_mul_right_Ioi g 0 hc,zero_mul,smul_eq_mul]
  rw [hI]
  have hF : (t / u) ^ 3 = c⁻¹ * c⁻¹ ^ 2 := by
    dsimp only [c]
    rw [inv_div]
    ring
  rw [hF,mul_assoc]
  exact mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr hc.le)

theorem ray_slope_integral {n : ℕ} {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (m d : Fin n → ℝ) (hd : ∀ j, 0 < d j) :
    (∫ s : ℝ in Ioi 0, pressureWeight p L s * rayWeight L m d s) =
      ∑ j, m j * imageTail (imageSlope p L) L (d j) := by
  let f (i : Fin n) (s : ℝ) := m i * (GammaMeasure.imageDensity p L s * s *
    (Real.exp (-s * d i) / (1 - Real.exp (-s * L))))
  have hI (i : Fin n) : IntegrableOn (f i) (Ioi 0) := (imageSlopeTail_integrable hp hL (hd i)).const_mul (m i)
  have hE (s : ℝ) : pressureWeight p L s * rayWeight L m d s = ∑ i, f i s := by
    dsimp only [pressureWeight,rayWeight,periodicDen,f]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hE s),integral_finsetSum _ (fun i _ => hI i)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [f]
  rw [integral_const_mul]
  exact congrArg (m i * ·) (imageSlope_samples_hasSum hp hL (hd i)).tsum_eq.symm

theorem root_rightRay_neighbor_lt {n : ℕ} (S : AnchoredCircleSource (Fin n)) {s : ℝ} (hs : 0 < s) :
    S.mass S.neighbor * Real.exp (-s) < rightRay S S.root s := by
  let L := S.period
  let e := S.forwardDistance S.root
  let j := S.neighbor
  have hOne : e j = 1 := by
    dsimp only [e,j]
    rw [S.forwardDistance_eq_sub S.root_neighbor_next.1,S.coordinate_root,S.coordinate_neighbor,sub_zero]
  have hDen := periodicDen_pos S.period_pos hs
  have hDenU : periodicDen L s < 1 := by unfold periodicDen; linarith only [Real.exp_pos (-s * L)]
  let v (k : Fin n) := S.mass k * (Real.exp (-s * e k) / periodicDen L s)
  have hTerm : S.mass j * Real.exp (-s) < v j := by
    dsimp only [v]
    rw [hOne,mul_one]
    exact mul_lt_mul_of_pos_left ((lt_div_iff₀ hDen).mpr
      (mul_lt_of_lt_one_right (Real.exp_pos (-s)) hDenU)) (S.mass_pos j)
  have hLe : v j ≤ ∑ k, v k := by
    refine Finset.single_le_sum ?_ (Finset.mem_univ j)
    intro k _
    dsimp only [v]
    exact mul_nonneg (S.mass_pos k).le (div_nonneg (Real.exp_pos _).le hDen.le)
  exact hTerm.trans_le hLe

theorem ray_slope_torque_eq {n : ℕ} {p : ℝ} (hp : 0 < p) (F : Configuration n p)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) (i : Fin n) :
    let S := C.source
    (∫ s : ℝ in Ioi 0, pressureWeight p S.period s * leftRay S i s) =
      ∫ s : ℝ in Ioi 0, pressureWeight p S.period s * rightRay S i s := by
  let S := C.source
  change (∫ s : ℝ in Ioi 0, pressureWeight p S.period s * rayWeight S.period S.mass (fun k => S.forwardDistance k i) s) =
    ∫ s : ℝ in Ioi 0, pressureWeight p S.period s * rayWeight S.period S.mass (S.forwardDistance i) s
  rw [ray_slope_integral hp S.period_pos S.mass _ (fun k => S.forwardDistance_pos k i),
    ray_slope_integral hp S.period_pos S.mass _ (S.forwardDistance_pos i)]
  exact (sub_eq_zero.mp (F.chart_torque_images C hp i)).symm

theorem root_right_slope_gt {n : ℕ} {p : ℝ} (hp : 0 < p) (S : AnchoredCircleSource (Fin n)) :
    S.mass S.neighbor * imageSlope p S.period 1 <
      ∫ s : ℝ in Ioi 0, pressureWeight p S.period s * rightRay S S.root s := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have h := integral_strict_of_ae_lt μ ((imageSlope_integrable hp S.period_pos zero_lt_one).const_mul
    (S.mass S.neighbor)) (ray_integrable hp S.period_pos S.mass _ (S.forwardDistance_pos S.root)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hW : 0 < pressureWeight p S.period s := mul_pos (imageDensity_pos hp S.period_pos hs) hs
      have h := mul_lt_mul_of_pos_left (root_rightRay_neighbor_lt S hs) hW
      change S.mass S.neighbor * (pressureWeight p S.period s * Real.exp (-s * 1)) <
        pressureWeight p S.period s * rightRay S S.root s
      rw [mul_one]
      simpa only [mul_left_comm] using h)
  rwa [integral_const_mul] at h

theorem pressure_unit_gt {n : ℕ} {p : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    let S := C.source
    let b := S.mass S.neighbor
    b * imageSlope p S.period 1 * (1 + b / 8) < pressureAt p S S.root := by
  let S := C.source
  let L := S.period
  let i := S.root
  let j := S.neighbor
  let b := S.mass j
  let W := pressureWeight p L
  let A := leftRay S i
  let B := rightRay S i
  let d (k : Fin n) := S.forwardDistance k i
  let e (k : Fin n) := S.forwardDistance i k
  have hL := S.period_pos
  have hb := S.mass_pos j
  have hD (k : Fin n) : 1 ≤ d k := by
    by_cases hk : k = i
    · subst k
      dsimp only [d]
      rw [S.forwardDistance_self]
      linarith only [S.period_ge_two]
    · have h := (S.forwardDistance_caps C.circular_caps hk).2
      change S.mass i ≤ d k at h
      simpa only [i,S.mass_root] using h
  have hA_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ A s := by
    unfold A leftRay rayWeight
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (S.mass_pos k).le (div_nonneg (Real.exp_pos _).le (periodicDen_pos hL hs).le)
  have hAi : IntegrableOn (fun s => W s * A s) (Ioi 0) := ray_integrable hp hL S.mass d (fun k => S.forwardDistance_pos k i)
  have hBi : IntegrableOn (fun s => W s * B s) (Ioi 0) := ray_integrable hp hL S.mass e (S.forwardDistance_pos i)
  have hAB : IntegrableOn (fun s => W s * (A s * B s)) (Ioi 0) :=
    rays_product_integrable hp hp₂ hL S.mass d e (fun k => S.forwardDistance_pos k i) (S.forwardDistance_pos i)
  have hShift : IntegrableOn (fun s => W s * (Real.exp (-s) * A s)) (Ioi 0) := by
    apply (ray_integrable hp hL S.mass (fun k => d k + 1) (fun k => by have := hD k; positivity)).congr
    exact Eventually.of_forall fun s => by dsimp only [W,A,leftRay]; rw [shifted_ray_eq]
  have hAeq := ray_slope_integral hp hL S.mass d (fun k => S.forwardDistance_pos k i)
  have hTor := ray_slope_torque_eq hp F C i
  change (∫ s : ℝ in Ioi 0, W s * A s) = ∫ s : ℝ in Ioi 0, W s * B s at hTor
  let U := imageSlope p L
  have hShiftBound : (1 / 8) * (∫ s : ℝ in Ioi 0, W s * A s) ≤
      ∫ s : ℝ in Ioi 0, W s * (Real.exp (-s) * A s) := by
    change (1 / 8) * (∫ s : ℝ in Ioi 0, pressureWeight p L s * rayWeight L S.mass d s) ≤ _
    rw [hAeq, setIntegral_congr_fun measurableSet_Ioi (g := fun s =>
      pressureWeight p L s * rayWeight L S.mass (fun k => d k + 1) s)
      (fun s _ => by dsimp only [W,A,leftRay]; rw [shifted_ray_eq]),
      ray_slope_integral hp hL S.mass _ (fun k => by have := hD k; positivity),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [show (1 / 8) * (S.mass k * imageTail U L (d k)) = S.mass k * ((1 / 8) * imageTail U L (d k)) by ring]
    apply mul_le_mul_of_nonneg_left _ (S.mass_pos k).le
    have hI := (imageSlope_samples_hasSum hp hL (S.forwardDistance_pos k i)).summable
    have hI' := (imageSlope_samples_hasSum hp hL (show 0 < d k + 1 by have := hD k; positivity)).summable
    unfold imageTail
    rw [← tsum_mul_left]
    apply (hI.mul_left (1 / 8)).tsum_le_tsum _ hI'
    intro n
    let t := d k + (n : ℝ) * L
    have ht : 1 ≤ t := le_add_of_nonneg_right (by positivity) |>.trans' (hD k)
    have ht₀ := zero_lt_one.trans_le ht
    have hU₀ : 0 ≤ U t := by
      unfold U imageSlope
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (mul_nonneg (imageDensity_pos hp hL hs).le (show 0 < s from hs).le) (Real.exp_pos _).le
    have hFrac : (1 / 2 : ℝ) ≤ t / (t + 1) := (le_div_iff₀ (by positivity)).mpr (by linarith only [ht])
    have hPow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hFrac 3
    have h := (mul_le_mul_of_nonneg_right hPow hU₀).trans
      (imageSlope_scaled_lower hp hp₂ hL ht₀ (by linarith : t ≤ t + 1))
    change (1 / 8) * U t ≤ U (d k + 1 + (n : ℝ) * L)
    rw [show d k + 1 + (n : ℝ) * L = t + 1 by dsimp only [t]; ring]
    exact (by norm_num : (1 / 8 : ℝ) = (1 / 2) ^ 3) ▸ h
  have hTB : b * U 1 < ∫ s : ℝ in Ioi 0, W s * B s := root_right_slope_gt hp S
  have hProd := setIntegral_mono_on (hShift.const_mul b) hAB measurableSet_Ioi (fun s hs => by
    have h := mul_le_mul_of_nonneg_left (root_rightRay_neighbor_lt S hs).le (hA_nonneg s hs)
    have hW : 0 ≤ W s := mul_nonneg (imageDensity_pos hp hL hs).le (show 0 < s from hs).le
    linarith only [mul_le_mul_of_nonneg_left h hW])
  rw [integral_const_mul] at hProd
  have hPi : pressureAt p S i = (∫ s : ℝ in Ioi 0, W s * (A s * B s)) + ∫ s : ℝ in Ioi 0, W s * B s := by
    unfold pressureAt
    rw [show S.mass i = 1 from S.mass_root]
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => W s * (A s * B s) + W s * B s)
      (fun s _ => by dsimp only [W,A,B]; ring),integral_add hAB hBi]
  have hS := mul_le_mul_of_nonneg_left hShiftBound hb.le
  rw [hTor] at hS
  have hT := mul_lt_mul_of_pos_left hTB (show 0 < 1 + b / 8 by positivity)
  change _ < pressureAt p S i
  rw [hPi]
  nlinarith only [hProd,hS,hT]

end ACS12.Pressure
