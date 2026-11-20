import ACS12.PressureMomentEnvelope

/-! The minimum's two actual rays pay the full pressure ceiling. -/
namespace ACS12.Pressure

open Set MeasureTheory CenteredCircle.AllN
open GammaMeasure (imageDensity_pos imagePotential imagePotential_samples_summable
  imageSlope imageSelf imageSelf_eq_tail)

theorem minimumRay_pressure_le {n : ℕ} {p L t C : ℝ}
    (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) (ht : 0 < t)
    (m d e : Fin n → ℝ) (hm : ∀ j, 0 < m j) (hd : ∀ j, 0 < d j) (he : ∀ j, 0 < e j)
    {i j : Fin n} (hj : j ≠ i) (hdL : d i = L) (hMin : ∀ k, m i ≤ m k)
    (hPeriod : 2 * m i ≤ L) (hGap : m j ≤ e j)
    (hR : nonselfRayRow L m d i (imagePotential p L) ≤ C / 2)
    (hScale : imagePotential p L t = C / (2 * m i))
    (hT : nonselfRayRow L m d i (imageSlope p L) = nonselfRayRow L m e i (imageSlope p L))
    (hRay : ∀ s > 0, rayWeight L m e s ≤ pressureBose (m i) s ∧
      rayWeight L m e s ≤ oppositeRayBose (m j) (e j) s) :
    ∃ u ≥ 1, u ^ 3 = m j / m i ∧
      (∫ s : ℝ in Ioi 0, pressureWeight p L s * ((rayWeight L m e s + m i) * rayWeight L m d s)) ≤
        C / 2 * max 1 (pressureNeighbor p u (m i / t)) + m i * imageSelf p L := by
  let a := m i
  let r := m j
  let g := e j
  let u := (r / a) ^ (1 / 3 : ℝ)
  let Z := max 1 (pressureNeighbor p u (a / t))
  let T := minimumAtomTest a r g
  let Ts := minimumAtomTest a a a
  let K := imagePotential p L
  let w := GammaMeasure.imageDensity p L
  let X := rayWeight L m d
  let Y := rayWeight L m e
  let I := Finset.univ.erase i
  let J : Finset (Fin n) := {i}
  let Xn (s : ℝ) := ∑ k ∈ I, m k * (Real.exp (-s * d k) / periodicDen L s)
  let Xs (s : ℝ) := ∑ k ∈ J, m k * (Real.exp (-s * d k) / periodicDen L s)
  have hp₁ : 1 ≤ p := by linarith only [hp]
  have hp₀ := zero_lt_one.trans_le hp₁
  have ha : 0 < a := hm i
  have hr : 0 < r := hm j
  have hC : 0 ≤ C := by
    have hK := GammaMeasure.imagePotential_pos hp₀ hL ht
    rw [hScale] at hK
    exact ((div_pos_iff_of_pos_right (by positivity : 0 < 2 * m i)).mp hK).le
  have hZ : 1 ≤ Z := le_max_left _ _
  have hu : 1 ≤ u := by
    have h := (one_le_div ha).mpr (hMin j)
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hCube : u ^ 3 = r / a := by
    unfold u
    rw [← Real.rpow_natCast,← Real.rpow_mul (div_nonneg hr.le ha.le)]
    norm_num
  have hrE : r = u ^ 3 * a := by rw [hCube,div_mul_cancel₀ _ ha.ne']
  have hR' : nonselfRayRow L m d i K ≤ m i * imagePotential p L t := by
    rw [hScale]
    convert hR using 1
    field_simp [(hm i).ne']
  obtain ⟨hD,hU⟩ := minimumTorque_quantum hp₁ hp₂ hL ht m d e hm hd he hj hMin hR' hT
  have hMT : Measurable T := by unfold T minimumAtomTest oppositeRayBose pressureBose periodicDen; fun_prop
  have hMS : Measurable Ts := by unfold Ts minimumAtomTest oppositeRayBose pressureBose periodicDen; fun_prop
  have hTB (s : ℝ) (hs : 0 < s) : 0 ≤ T s ∧ T s ≤ a * s + 1 :=
    minimumAtomTest_bounds ha.le hr hGap hs
  have hSB (s : ℝ) (hs : 0 < s) : 0 ≤ Ts s ∧ Ts s ≤ a * s + 1 :=
    minimumAtomTest_bounds ha.le ha le_rfl hs
  obtain ⟨hIN,hNE⟩ := testedRay_integral hp₀ hL ha.le m d hd I hMT hTB
  obtain ⟨hIS,hSE⟩ := testedRay_integral hp₀ hL ha.le m d hd J hMS hSB
  change IntegrableOn (fun s => w s * T s * Xn s) (Ioi 0) at hIN
  change IntegrableOn (fun s => w s * Ts s * Xs s) (Ioi 0) at hIS
  change (∫ s : ℝ in Ioi 0, w s * T s * Xn s) = _ at hNE
  change (∫ s : ℝ in Ioi 0, w s * Ts s * Xs s) = _ at hSE
  have hN : (∫ s : ℝ in Ioi 0, w s * T s * Xn s) ≤ Z * nonselfRayRow L m d i K := by
    rw [hNE,nonselfRayRow,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [mul_left_comm Z]
    apply mul_le_mul_of_nonneg_left _ (hm k).le
    have hdk : t ≤ d k := hD k (Finset.mem_erase.mp hk).1
    unfold imageTail
    rw [← tsum_mul_left]
    apply (testedImage_samples hp₀ hL ha.le (hd k) hMT hTB).2.summable.tsum_le_tsum
      _ ((imagePotential_samples_summable hp₀ hL (hd k)).mul_left Z)
    intro l
    have hx := hdk.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg l) hL.le))
    have h := minimumAtom_moment_le hp hp₂ hL ha.le hr hGap ht hx hu hU hrE
    simpa only [testedImage,mul_right_comm] using h
  have hS : (∫ s : ℝ in Ioi 0, w s * Ts s * Xs s) ≤ a * imageSelf p L := by
    rw [hSE,Finset.sum_singleton,hdL,imageSelf_eq_tail]
    apply mul_le_mul_of_nonneg_left _ ha.le
    unfold imageTail
    rw [← tsum_mul_left]
    apply (testedImage_samples hp₀ hL ha.le hL hMS hSB).2.summable.tsum_le_tsum
      _ ((imagePotential_samples_summable hp₀ hL hL).mul_left 2)
    intro l
    have hx : L ≤ L + (l : ℝ) * L := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg l) hL.le)
    exact testedImage_self_le hp₀ hp₂ hL ha (hL.trans_le hx) (hPeriod.trans hx)
  have hF (s : ℝ) : X s = Xn s + Xs s := by
    unfold X rayWeight Xn Xs I J
    rw [Finset.sum_singleton]
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have hP (s : ℝ) (hs : 0 < s) :
      pressureWeight p L s * ((Y s + a) * X s) ≤ w s * T s * Xn s + w s * Ts s * Xs s := by
    obtain ⟨hY,hY'⟩ := hRay s hs
    have hPos (k : Fin n) : 0 ≤ m k * (Real.exp (-s * d k) / periodicDen L s) :=
      mul_nonneg (hm k).le (div_nonneg (Real.exp_pos _).le (periodicDen_pos hL hs).le)
    have hXn : 0 ≤ Xn s := Finset.sum_nonneg fun k _ => hPos k
    have hXs : 0 ≤ Xs s := Finset.sum_nonneg fun k _ => hPos k
    have hS : oppositeRayBose a a s = pressureBose a s := by
      simp only [oppositeRayBose,sub_self,neg_zero,zero_mul,Real.exp_zero,one_mul]
    have h1 : s * (Y s + a) ≤ T s := by
      unfold T minimumAtomTest
      exact mul_le_mul_of_nonneg_left (by linarith only [hY']) hs.le
    have h2 : s * (Y s + a) ≤ Ts s := by
      unfold Ts minimumAtomTest
      rw [hS]
      exact mul_le_mul_of_nonneg_left (by linarith only [hY]) hs.le
    have hW := (imageDensity_pos hp₀ hL hs).le
    have hn := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hXn) hW
    have hs' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hXs) hW
    rw [hF]
    dsimp only [pressureWeight,w] at hn hs' ⊢
    linarith only [hn,hs']
  have hAI := ray_integrable hp₀ hL m d hd
  have hAB := rays_product_integrable hp₀ hp₂ hL m e d he hd
  have hPressure : IntegrableOn (fun s => pressureWeight p L s * ((Y s + a) * X s)) (Ioi 0) :=
    (hAB.add (hAI.const_mul a)).congr (Filter.Eventually.of_forall fun s => by
      simp only [Pi.add_apply,X,Y]
      ring)
  have hI : IntegrableOn (fun s => w s * T s * Xn s + w s * Ts s * Xs s) (Ioi 0) := hIN.add hIS
  have h := setIntegral_mono_on hPressure hI measurableSet_Ioi (fun s hs => hP s hs)
  rw [integral_add hIN hIS] at h
  refine ⟨u,hu,hCube,?_⟩
  have hRZ := mul_le_mul_of_nonneg_left hR (zero_le_one.trans hZ)
  have hP' := h.trans (add_le_add hN hS)
  change _ ≤ C / 2 * Z + _
  linarith only [hP',hRZ]

end ACS12.Pressure
