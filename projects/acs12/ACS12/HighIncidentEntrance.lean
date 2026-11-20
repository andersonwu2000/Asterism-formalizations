import ACS12.HighIncidentActual
import ACS12.HighIncidentFeeLaw
import ACS12.PressureIncidentRay

/-! The original attained adjacent mass over the entire lower high-exponent band. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN Pressure

private theorem highIncident_samples_summable {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t)
    (kind : CircleKernelKind) :
    Summable (fun j : ℕ => imageMoment p L kind 0 (t + (j : ℝ) * L)) := by
  let g (s : ℝ) := imageDensity p L s * densityPolynomial kind s
  let H (s : ℝ) := g s * (Real.exp (-s * t) / periodicDen L s)
  have hg : Measurable g := ((continuous_imageDensity hp hL).mul (continuous_densityPolynomial kind)).measurable
  have hG (s : ℝ) (hs : 0 < s) : 0 ≤ g s :=
    mul_nonneg (imageDensity_pos hp hL hs).le (densityPolynomial_pos kind hs).le
  have hI : IntegrableOn H (Ioi 0) := by
    apply (imageSlopeTail_integrable hp hL ht).mono'
    · have hm : Measurable H := by
        unfold H periodicDen
        exact hg.mul (by fun_prop)
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      have hE := div_pos (Real.exp_pos (-s * t)) (periodicDen_pos hL hs₀)
      have hb : polyB s ≤ s := by unfold polyB; linarith only [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs₀.le)]
      have hk : densityPolynomial kind s ≤ s := by
        cases kind with
        | a => exact (polyA_lt_polyB hs₀).le.trans hb
        | b => exact hb
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (imageDensity_pos hp hL hs₀).le) hE.le
      rw [Real.norm_of_nonneg (show 0 ≤ H s from mul_nonneg (hG s hs₀) hE.le)]
      exact h
  simpa only [H,g,imageMoment,imageMomentWeight,pow_zero,one_mul,periodicDen] using
    (hasSum_laplace_samples g hg hG hL hI).summable

private theorem highIncident_rightExterior_ratio {n : ℕ} {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4)
    (S : AnchoredCircleSource (Fin n)) (hCap : S.HasCircularMassCaps) (hb : S.mass S.neighbor ≤ 5 / 8) :
    (S.mass S.neighbor / ((p + 4) / 2)) * S.rightExterior (imageB p S.period) ≤
      S.rightExterior (imageA p S.period) := by
  let b := S.mass S.neighbor
  let L := S.period
  have hb₀ : 0 < b := S.mass_pos _
  have hp₀ : 0 < p := by linarith only [hp]
  have hσ : 0 < (p + 4) / 2 := by positivity
  have hL : 0 < L := S.period_pos
  unfold AnchoredCircleSource.rightExterior
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (S.mass_pos i).le
  let t := S.rightDistance i
  have ht := S.rightDistance_pos i
  change b / ((p + 4) / 2) * imageTail (imageB p L) L t ≤ imageTail (imageA p L) L t
  rw [← imageTail_moment_zero_a hp₀ hL ht,← imageTail_moment_zero_b hp₀ hL ht]
  unfold imageTail
  rw [← tsum_mul_left]
  apply ((highIncident_samples_summable hp₀ hL ht .b).mul_left _).tsum_le_tsum _
    (highIncident_samples_summable hp₀ hL ht .a)
  intro j
  let x := t + (j : ℝ) * L
  have hx : b ≤ x := (S.rightDistance_ge_neighbor hCap i).trans (le_add_of_nonneg_right (by positivity))
  have h := highIncident_actualPeano_ratio hp hP hL hb₀ hb hx
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ hσ).mpr (h.trans_eq (mul_comm _ _)) |>.le

private theorem highIncident_fee_identity {u c s : ℝ} (hs : 0 < s) :
    pressureBose 1 s * ((1 - u) * s - (polyB s - c * polyA s)) =
      Real.exp (-s) * highIncidentFeeRaw u c s := by
  unfold pressureBose periodicDen polyA polyB highIncidentFeeRaw expHeadFactor
  simp only [mul_one,one_mul]
  field_simp [(expHead_den_pos hs).ne']
  ring

private theorem highIncident_fee_point {n : ℕ} {p u c : ℝ} (hp : 0 < p)
    (S : AnchoredCircleSource (Fin n)) (hCap : S.HasCircularMassCaps) {s : ℝ} (hs : 0 < s) :
    (1 - u) * (pressureWeight p S.period s * leftRay S S.root s) ≤
      imageDensity p S.period s * polyB s * leftRay S S.root s -
        c * (imageDensity p S.period s * polyA s * leftRay S S.root s) +
        imageDensity p S.period s * Real.exp (-s) * highIncidentFeeTest u c s := by
  let X := leftRay S S.root s
  let A := (1 - u) * s - (polyB s - c * polyA s)
  have hX : 0 ≤ X := rayWeight_nonneg S.period_pos hs (fun i => (S.mass_pos i).le) _
  have hF : pressureBose 1 s * A = Real.exp (-s) * highIncidentFeeRaw u c s := highIncident_fee_identity hs
  have hFee : A * X ≤ Real.exp (-s) * highIncidentFeeTest u c s := by
    rcases le_total 0 A with h | h
    · calc
        _ ≤ A * pressureBose 1 s := mul_le_mul_of_nonneg_left (leftRay_root_le_bose S hCap hs) h
        _ = Real.exp (-s) * highIncidentFeeRaw u c s := by rw [mul_comm A,hF]
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le
    · exact (mul_nonpos_of_nonpos_of_nonneg h hX).trans (mul_nonneg (Real.exp_pos _).le (le_max_left _ _))
  have h := mul_le_mul_of_nonneg_left hFee (imageDensity_pos hp S.period_pos hs).le
  dsimp only [A,X,pressureWeight] at h ⊢
  nlinarith only [h]

theorem _root_.ACS12.Configuration.occupiedEdge_fee_required {n : ℕ} {p u : ℝ}
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (hp : 0 < p) (hu : 0 ≤ u) (hu₁ : u < 1)
    (hR : u * C.source.mass C.source.neighbor * C.source.rightExterior (imageB p C.source.period) ≤
      C.source.rightExterior (imageA p C.source.period)) :
    let S := C.source
    let b := S.mass S.neighbor
    (1 - b) * (1 + u * b) * (imagePotential p S.period 1 + imageSelf p S.period) <
      highIncidentActualFee p S.period u (u * b) := by
  dsimp only
  let S := C.source
  let L := S.period
  let b := S.mass S.neighbor
  let c := u * b
  let K := imagePotential p L 1
  let U := imageSlope p L 1
  let D := K + imageSelf p L
  let X := leftRay S S.root
  let T := ∫ s : ℝ in Ioi 0, pressureWeight p L s * X s
  have hp₀ := hp
  have hL : 0 < L := S.period_pos
  have hb : 0 < b := S.mass_pos _
  have hc : 0 ≤ c := mul_nonneg hu hb.le
  have hθ : 0 < 1 - u := sub_pos.mpr hu₁
  have hT : b * U < T := by
    unfold T X
    rw [ray_slope_torque_eq hp₀ F C S.root]
    exact root_right_slope_gt hp₀ S
  have hFeeI := highIncidentActualFee_integrable hp₀ hL hu hc
  obtain ⟨hIA,hA⟩ := leftRay_root_moment_integral hp₀ S .a
  obtain ⟨hIB,hB'⟩ := leftRay_root_moment_integral hp₀ S .b
  have hTI : IntegrableOn (fun s => pressureWeight p L s * X s) (Ioi 0) :=
    ray_integrable hp₀ hL S.mass _ (S.forwardDistance_pos · S.root)
  let A (s : ℝ) := imageDensity p L s * polyA s * X s
  let B (s : ℝ) := imageDensity p L s * polyB s * X s
  let f (s : ℝ) := imageDensity p L s * Real.exp (-s) * highIncidentFeeTest u c s
  have hIA' : IntegrableOn A (Ioi 0) := hIA
  have hIB' : IntegrableOn B (Ioi 0) := hIB
  have hf : IntegrableOn f (Ioi 0) := hFeeI
  have h : (∫ s : ℝ in Ioi 0, (1 - u) * (pressureWeight p L s * X s)) ≤
      ∫ s : ℝ in Ioi 0, B s - c * A s + f s := by
    exact setIntegral_mono_on (hTI.const_mul _) ((hIB'.sub (hIA'.const_mul c)).add hf)
      measurableSet_Ioi (fun s hs => highIncident_fee_point hp₀ S C.circular_caps hs)
  rw [integral_const_mul,integral_add (f := fun s => B s - c * A s) (hIB'.sub (hIA'.const_mul c)) hf,
    integral_sub hIB' (hIA'.const_mul c),integral_const_mul] at h
  change (1 - u) * T ≤ _ at h
  change (∫ s : ℝ in Ioi 0, A s) = S.leftExterior (imageA p L) at hA
  change (∫ s : ℝ in Ioi 0, B s) = S.leftExterior (imageB p L) at hB'
  rw [hA,hB'] at h
  change _ ≤ _ - _ + highIncidentActualFee p L u c at h
  change c * S.rightExterior (imageB p L) ≤ S.rightExterior (imageA p L) at hR
  obtain ⟨h₁,h₂⟩ := F.anchored_image_balances hp₀ C
  change S.leftExterior (imageA p L) + S.rightExterior (imageB p L) = U + (1 - b) * D at h₁
  change S.leftExterior (imageB p L) + S.rightExterior (imageA p L) = b * U - (1 - b) * D at h₂
  have hTU := mul_lt_mul_of_pos_left hT hθ
  have hCancel : (1 - u) * (b * U) = (b - c) * U := by unfold c; ring
  rw [hCancel] at hTU
  change (1 - b) * (1 + c) * D < highIncidentActualFee p L u c
  nlinarith only [h,hR,hTU,h₂,congrArg (c * ·) h₁]

theorem _root_.ACS12.Configuration.highIncident_neighbor_mass_gt {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hp : 2 ≤ p) (hP : p ≤ 4) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) :
    (12 - p) / 16 < C.source.mass C.source.neighbor := by
  let S := C.source
  let L := S.period
  let b := S.mass S.neighbor
  let u := 2 / (p + 4)
  let c := u * b
  let β := 1 - 1 / (8 * u)
  let K := imagePotential p L 1
  let D := K + imageSelf p L
  have hp₀ : 0 < p := by linarith only [hp]
  have hL : 0 < L := S.period_pos
  have hb : 0 < b := S.mass_pos _
  have hb₁ : b ≤ 1 := S.mass_neighbor_le_one
  have hu₀ : 0 < u := by unfold u; positivity
  have hu : 1 / 4 ≤ u := by
    unfold u
    apply (le_div_iff₀ (show 0 < p + 4 by positivity)).mpr
    linarith only [hP]
  have hu' : u ≤ 1 / 3 := by
    unfold u
    apply (div_le_iff₀ (show 0 < p + 4 by positivity)).mpr
    linarith only [hp]
  have hβ : β = (12 - p) / 16 := by
    unfold β u
    field_simp [show p + 4 ≠ 0 by positivity]
    ring
  rw [← hβ]
  by_contra! hB
  have hbU : b ≤ 5 / 8 := by rw [hβ] at hB; linarith only [hp,hB]
  have hc : 0 ≤ c := mul_nonneg hu₀.le hb.le
  have hβu : u * β = u - 1 / 8 := by
    unfold β
    field_simp [hu₀.ne'] <;> ring
  have hcU : c ≤ u - 1 / 8 := hβu ▸ mul_le_mul_of_nonneg_left hB hu₀.le
  have hFee := highIncidentActualFee_lt hp hL hu hu' hc hcU
  have hR := highIncident_rightExterior_ratio hp hP S C.circular_caps hbU
  have hC : b / ((p + 4) / 2) = c := by
    unfold c u
    field_simp [show p + 4 ≠ 0 by positivity]
  change b / ((p + 4) / 2) * S.rightExterior (imageB p L) ≤ S.rightExterior (imageA p L) at hR
  rw [hC] at hR
  have hNeeded : (1 - b) * (1 + c) * D < highIncidentActualFee p L u c :=
    F.occupiedEdge_fee_required C hp₀ hu₀.le (by linarith only [hu']) hR
  have hPrice : 31 / 40 - (39 / 40) * u < (1 - b) * (1 + c) := by
    have hC : (1 - β) * (1 + u * β) ≤ (1 - b) * (1 + c) := by
      have h := mul_nonneg (sub_nonneg.mpr hB) (show 0 ≤ 1 - u + u * (β + b) by
        have hβ₀ := hb.le.trans hB
        have hSum := mul_nonneg hu₀.le (add_nonneg hβ₀ hb.le)
        linarith only [hu',hSum])
      unfold c
      nlinarith only [h]
    have hE : (1 - β) * (1 + u * β) = 7 / (64 * u) + 1 / 8 := by
      rw [hβu]
      unfold β
      field_simp [hu₀.ne']
      ring
    rw [hE] at hC
    apply lt_of_lt_of_le _ hC
    apply (mul_lt_mul_iff_right₀ (show 0 < 320 * u by positivity)).mp
    field_simp [hu₀.ne']
    nlinarith only [sq_nonneg (u - 1 / 3)]
  have hK := imagePotential_pos hp₀ hL zero_lt_one
  have hD : K ≤ D := le_add_of_nonneg_right (imageSelf_pos hp₀ hL).le
  have hCost := mul_nonneg (sub_nonneg.mpr hb₁) (show 0 ≤ 1 + c by positivity)
  exact hNeeded.not_ge (hFee.le.trans ((mul_le_mul_of_nonneg_left hPrice.le hK.le).trans
    ((mul_comm K _).trans_le (mul_le_mul_of_nonneg_left hD hCost))))

end ACS12.GammaMeasure
