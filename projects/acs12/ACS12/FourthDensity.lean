import ACS12.FourthSlopeSigns

/-! The integral form of the original fourth row and its pointwise variation. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter

noncomputable def fourthDensity (u v r m s : ℝ) : ℝ :=
  polyB (v * s) * fourthFirstStream u s + polyA (v * s) * scaledExpTail s r -
    v * r * s * Real.exp (-s * v) + (m - r) * Real.exp (-s * v)

theorem fourthSourceRow_integral {p L θ u v r m : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hu : 0 < u) (hv : 0 < v) (hr : 0 < r) :
    IntegrableOn (fun s => lawDensity p L θ s * fourthDensity u v r m s) (Ioi 0) ∧
      fourthSourceRow p L θ u v r m =
        (∫ s : ℝ in Ioi 0, lawDensity p L θ s * fourthDensity u v r m s) +
          (m - r) * lawSelf p L θ := by
  let w := lawDensity p L θ
  let f (s : ℝ) := lawPeanoDensity p L θ v .b s * Real.exp (-s * u)
  let g (s : ℝ) := f s * scaledExpTail s 1
  let h (s : ℝ) := lawPeanoDensity p L θ v .a s * scaledExpTail s r
  let k (s : ℝ) := w s * s * Real.exp (-s * v)
  let l (s : ℝ) := w s * Real.exp (-s * v)
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hf : Integrable f μ := lawPeanoKernel_integrable hp hp₂ hL hθ hv hu .b
  obtain ⟨hg, hgE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hv hu.le zero_lt_one .b
  obtain ⟨hh, hhE⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hv (t := 0) le_rfl hr .a
  simp only [mul_zero, Real.exp_zero, mul_one] at hh hhE
  have hgI : Integrable g μ := hg
  have hhI : Integrable h μ := hh
  have hk : Integrable k μ := by simpa only [pow_one] using lawMoment_integrable hp hp₂ hL hθ hv 1
  have hl : Integrable l μ := by simpa only [pow_zero, mul_one] using lawMoment_integrable hp hp₂ hL hθ hv 0
  have hI : Integrable (fun s => u * f s + g s + h s - (v * r) * k s) μ :=
    (((hf.const_mul u).add hgI).add hhI).sub (hk.const_mul (v * r))
  have hPoint (s : ℝ) :
      w s * fourthDensity u v r m s = u * f s + g s + h s - (v * r) * k s + (m - r) * l s := by
    simp only [fourthDensity, fourthFirstStream, f, g, h, k, l, lawPeanoDensity, densityPolynomial, w]
    ring
  constructor
  · exact (hI.add (hl.const_mul (m - r))).congr (Eventually.of_forall fun s => (hPoint s).symm)
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hPoint x)]
    have hE := integral_four_terms hf hgI hhI hk u 1 (-1) (v * r)
    simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hE
    rw [integral_add hI (hl.const_mul (m - r)), hE, integral_const_mul, fourthSourceRow,
      hgE, hhE, lawPeanoKernel, signedLaplace]
    simp only [f, g, h, k, l, lawMoment, pow_one, pow_zero, mul_one, w, μ]
    ring

theorem expHeadFactor_eq_scaledExpTail {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    expHeadFactor (r * s) = s * (r + scaledExpTail s r) := by
  rw [expHeadFactor_eq_add_expTail (mul_pos hr hs), scaledExpTail_eq_factor hs, mul_comm r s]
  field_simp [hs.ne']

theorem fourthDensity_hasDerivAt {u v r m s dv dr dm t : ℝ} (hs : 0 < s)
    (hr : 0 < r + dr * t) :
    HasDerivAt (fun x => fourthDensity u (v + dv * x) (r + dr * x) (m + dm * x) s)
      (dv * fourthV u (v + dv * t) (r + dr * t) (m + dm * t) s -
        dr * fourthD (v + dv * t) (r + dr * t) s +
        dm * Real.exp (-s * (v + dv * t))) t := by
  have hV := ((hasDerivAt_id t).const_mul dv).const_add v
  have hR := ((hasDerivAt_id t).const_mul dr).const_add r
  have hM := ((hasDerivAt_id t).const_mul dm).const_add m
  have hV' : HasDerivAt (fun x : ℝ => v + dv * x) dv t := by simpa only [id_eq, mul_one] using hV
  have hR' : HasDerivAt (fun x : ℝ => r + dr * x) dr t := by simpa only [id_eq, mul_one] using hR
  have hM' : HasDerivAt (fun x : ℝ => m + dm * x) dm t := by simpa only [id_eq, mul_one] using hM
  have hX := hV'.mul_const s
  have hA := (hasDerivAt_polyA ((v + dv * t) * s)).comp t hX
  have hB := ((hasDerivAt_polyB ((v + dv * t) * s)).comp t hX).mul_const (fourthFirstStream u s)
  have hβ := (scaledExpTail_derivative hs hr).comp t hR'
  have hY := (hV'.const_mul (-s)).exp
  have hVR := ((hV'.mul hR').mul_const s).mul hY
  have hMR := (hM'.sub hR').mul hY
  have h := ((hB.add (hA.mul hβ)).sub hVR).add hMR
  convert h using 1
  have hHead : expHeadFactor (s * (r + dr * t)) = s * (r + dr * t + scaledExpTail s (r + dr * t)) := by
    rw [mul_comm s (r + dr * t)]
    exact expHeadFactor_eq_scaledExpTail hs hr
  simp only [fourthV, fourthD, Pi.mul_apply, Pi.sub_apply, Function.comp_apply,
    show -((v + dv * t) * s) = -s * (v + dv * t) by ring, mul_comm (r + dr * t) s, hHead]
  ring

end ACS12.GammaMeasure
