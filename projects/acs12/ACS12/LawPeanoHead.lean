import ACS12.FourthRootMotion

/-! The complete left-mesh Peano transform used by the coupled root. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

theorem lawPeanoHead_sampling {p L θ h t q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (ht : 0 < t) (hq : 0 < q)
    (kind : CircleKernelKind) :
    let g := lawPeanoDensity p L θ h kind
    IntegrableOn (fun s => g s * Real.exp (-s * t) * (q + scaledExpTail s q)) (Ioi 0) ∧
      samplingHead (lawPeanoKernel p L θ h kind) t q =
        ∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * (q + scaledExpTail s q) := by
  let g := lawPeanoDensity p L θ h kind
  let K := lawPeanoKernel p L θ h kind
  obtain ⟨B, _, hB⟩ := lawPeanoDensity_quadratic_bound hp hp₂ hL hθ hh kind
  obtain ⟨hTail, hTE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hh ht.le hq kind
  have hH := lawPeanoKernel_integrable hp hp₂ hL hθ hh ht kind
  have hSum : Summable (fun j : ℕ => K (t + j * q)) := by
    have hs := (hasSum_signedTail (t := t) (q := q)
      (lawPeanoDensity_measurable (θ := θ) (h := h) (zero_lt_one.trans_le hp) hL kind)
      hB ht.le hq).summable
    apply (summable_nat_add_iff 1).mp
    refine hs.congr fun j => ?_
    push_cast
    exact congrArg K (by ring)
  have hEq (s : ℝ) : q * (g s * Real.exp (-s * t)) +
      g s * Real.exp (-s * t) * scaledExpTail s q =
        g s * Real.exp (-s * t) * (q + scaledExpTail s q) := by ring
  constructor
  · exact ((hH.const_mul q).add hTail).congr (Eventually.of_forall hEq)
  · change samplingHead K t q = _
    rw [samplingHead_split K t q hSum, show samplingTail K t q = _ from hTE]
    change q * (∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t)) +
      (∫ s : ℝ in Ioi 0, g s * Real.exp (-s * t) * scaledExpTail s q) = _
    rw [← integral_const_mul, ← integral_add (hH.const_mul q) hTail]
    exact integral_congr_ae (Eventually.of_forall hEq)

theorem lawPeanoHead_mono_step {p L θ h t q₁ q₂ : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (ht : 0 < t)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hqq : q₁ ≤ q₂) (kind : CircleKernelKind) :
    samplingHead (lawPeanoKernel p L θ h kind) t q₁ ≤
      samplingHead (lawPeanoKernel p L θ h kind) t q₂ := by
  obtain ⟨h1, h1E⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hh ht hq₁ kind
  obtain ⟨h2, h2E⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hh ht hq₂ kind
  rw [h1E, h2E]
  apply integral_mono_ae h1 h2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  apply mul_le_mul_of_nonneg_left _ (mul_pos (lawPeanoDensity_pos (zero_lt_one.trans_le hp)
    hL hθ hh hs₀ kind) (Real.exp_pos _)).le
  apply le_of_mul_le_mul_left ?_ hs₀
  rw [← expHeadFactor_eq_scaledExpTail hs₀ hq₁, ← expHeadFactor_eq_scaledExpTail hs₀ hq₂]
  exact strictMonoOn_expHeadFactor.monotoneOn (mul_pos hq₁ hs₀) (mul_pos hq₂ hs₀)
    (mul_le_mul_of_nonneg_right hqq hs₀.le)

private theorem expHead_gt_two_E {x : ℝ} (hx : 0 < x) : 2 * BoseShape.E x < expHeadFactor x := by
  have hD : HasDerivAt expHeadFactor (BoseShape.E x) x := by
    apply ((hasDerivAt_id x).add (BoseShape.expTail_derivative hx)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact expHeadFactor_eq_add_expTail ht
  have he : BoseShape.E x = (1 - Real.exp (-x) - x * Real.exp (-x)) / (1 - Real.exp (-x)) ^ 2 :=
    hD.deriv.symm.trans (hasDerivAt_expHeadFactor hx).deriv
  have hE : expHeadFactor x - 2 * BoseShape.E x =
      (x - 2 + (x + 2) * Real.exp (-x)) / (1 - Real.exp (-x)) ^ 2 := by
    rw [he, expHeadFactor]
    field_simp [(expHead_den_pos hx).ne']
    ring
  apply sub_pos.mp
  rw [hE]
  have h := (lt_div_iff₀ (expHead_den_pos hx)).mp (BoseShape.expHeadFactor_gt_one_add_half hx)
  exact div_pos (by linarith only [h]) (sq_pos_of_pos (expHead_den_pos hx))

private theorem completeHeadExp_strictAnti {s v q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    StrictAntiOn (fun t => Real.exp (-s * (v + t)) * (q + 2 * t + scaledExpTail s (q + 2 * t)))
      (Ici 0) := by
  let f (t : ℝ) := Real.exp (-s * (v + t)) * (q + 2 * t + scaledExpTail s (q + 2 * t))
  have hD (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt f
        (Real.exp (-s * (v + t)) *
          (2 * BoseShape.E (s * (q + 2 * t)) - expHeadFactor ((q + 2 * t) * s))) t := by
    have hQ : HasDerivAt (fun x : ℝ => q + 2 * x) 2 t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (2 : ℝ)).const_add q
    have hQ₀ : 0 < q + 2 * t := add_pos_of_pos_of_nonneg hq (mul_nonneg zero_le_two ht)
    have hR := (scaledExpTail_derivative hs hQ₀).comp t hQ
    have hV : HasDerivAt (fun x : ℝ => v + x) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t).const_add v
    have hE := (hV.const_mul (-s)).exp
    convert hE.mul (hQ.add hR) using 1
    simp only [expHeadFactor_eq_scaledExpTail hs hQ₀, BoseShape.E, Pi.add_apply, Function.comp_apply, mul_one]
    ring
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun t ht => (hD t ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht₀ : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [(hD t ht₀.le).deriv]
    have h := expHead_gt_two_E (mul_pos (add_pos_of_pos_of_nonneg hq
      (mul_nonneg zero_le_two ht₀.le)) hs)
    rw [mul_comm (q + 2 * t) s] at h ⊢
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (sub_neg.mpr h)

theorem lawPeanoHead_advance_lt {p L θ h v q d : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h)
    (hv : 0 < v) (hq : 0 < q) (hd : 0 < d) (kind : CircleKernelKind) :
    samplingHead (lawPeanoKernel p L θ h kind) (v + d) (q + 2 * d) <
      samplingHead (lawPeanoKernel p L θ h kind) v q := by
  have hq' := add_pos hq (mul_pos two_pos hd)
  obtain ⟨h1, h1E⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hh hv hq kind
  obtain ⟨h2, h2E⟩ := lawPeanoHead_sampling hp hp₂ hL hθ hh (add_pos hv hd) hq' kind
  rw [h1E, h2E]
  letI : NeZero (volume.restrict (Ioi (0 : ℝ))) := ⟨positiveHalfLine_ne_zero⟩
  apply integral_strict_of_ae_lt _ h2 h1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have h := completeHeadExp_strictAnti (v := v) (mem_Ioi.mp hs) hq
    (mem_Ici.mpr (le_refl (0 : ℝ))) (show d ∈ Ici 0 from hd.le) hd
  simp only [add_zero, mul_zero] at h
  have hG := mul_lt_mul_of_pos_left h (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hh hs kind)
  simpa only [mul_assoc] using hG

end ACS12.GammaMeasure

