import ACS12.LawPeanoHead

/-! Joint continuity of the complete Peano head as base and spacing move. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open scoped Topology

theorem lawPeanoHead_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {p L θ h t q : ℝ} {T Q : ι → ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (hθ : θ ∈ Icc (0 : ℝ) 1) (hh : 0 < h)
    (ht : 0 < t) (hq : 0 < q) (hT : Tendsto T l (𝓝 t)) (hQ : Tendsto Q l (𝓝 q))
    (kind : CircleKernelKind) :
    Tendsto (fun x => samplingHead (lawPeanoKernel p L θ h kind) (T x) (Q x)) l
      (𝓝 (samplingHead (lawPeanoKernel p L θ h kind) t q)) := by
  let g := lawPeanoDensity p L θ h kind
  let f (t q s : ℝ) := g s * Real.exp (-s * t) * (q + scaledExpTail s q)
  let μ := volume.restrict (Ioi (0 : ℝ))
  let d := t / 2
  let e := q / 2
  have hd : 0 < d := half_pos ht
  have he : 0 < e := half_pos hq
  have hDt : d < t := by dsimp only [d]; linarith
  have hEq : e < q := by dsimp only [e]; linarith
  have hH := lawPeanoKernel_integrable hp hp₂ hL hθ hh hd kind
  obtain ⟨hE, _⟩ := lawPeanoTail_sampling hp hp₂ hL hθ hh hd.le he kind
  let b (s : ℝ) := g s * Real.exp (-s * d) * ((q + 1) + scaledExpTail s e)
  have hb : Integrable b μ := ((hH.const_mul (q + 1)).add hE).congr
    (Eventually.of_forall fun s => by dsimp only [g, b, Pi.add_apply]; ring)
  have hg := lawPeanoDensity_measurable (θ := θ) (h := h) (zero_lt_one.trans_le hp) hL kind
  have hNE : ∀ᶠ x in l, d < T x ∧ Q x ∈ Ioo e (q + 1) :=
    (hT.eventually (Ioi_mem_nhds hDt)).and (hQ.eventually (Ioo_mem_nhds hEq (by linarith)))
  have hLim : Tendsto (fun x => ∫ s : ℝ, f (T x) (Q x) s ∂μ) l (𝓝 (∫ s : ℝ, f t q s ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence b
    · exact Eventually.of_forall fun x => ((hg.mul (by fun_prop)).mul
        (show Measurable (fun s => Q x + scaledExpTail s (Q x)) by unfold scaledExpTail; fun_prop)).aestronglyMeasurable
    · filter_upwards [hNE] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs₀ : 0 < s := hs
      have hQ₀ : 0 < Q x := he.trans hx.2.1
      have hg₀ : 0 ≤ g s := (lawPeanoDensity_pos (zero_lt_one.trans_le hp) hL hθ hh hs₀ kind).le
      have hβ₀ : 0 ≤ scaledExpTail s (Q x) := (div_pos hQ₀ (expTail_den_pos (mul_pos hs₀ hQ₀))).le
      have hβ : scaledExpTail s (Q x) ≤ scaledExpTail s e :=
        (scaledExpTail_strictAnti hs₀).antitoneOn he hQ₀ hx.2.1.le
      have hT' : Real.exp (-s * T x) ≤ Real.exp (-s * d) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx.1.le (neg_nonpos.mpr hs₀.le))
      change ‖g s * Real.exp (-s * T x) * (Q x + scaledExpTail s (Q x))‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hg₀ (Real.exp_pos _).le)
        (add_nonneg hQ₀.le hβ₀))]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hT' hg₀) (add_le_add hx.2.2.le hβ)
        (add_nonneg hQ₀.le hβ₀) (mul_nonneg hg₀ (Real.exp_pos _).le)
    · exact hb
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hβ := (scaledExpTail_derivative (mem_Ioi.mp hs) hq).continuousAt.tendsto.comp hQ
      have he' := (Real.continuous_exp.continuousAt.tendsto.comp (hT.const_mul (-s)))
      exact (tendsto_const_nhds.mul he').mul (hQ.add hβ)
  rw [(lawPeanoHead_sampling hp hp₂ hL hθ hh ht hq kind).2]
  apply hLim.congr'
  filter_upwards [hNE] with x hx
  exact (lawPeanoHead_sampling hp hp₂ hL hθ hh (hd.trans hx.1) (he.trans hx.2.1) kind).2.symm

end ACS12.GammaMeasure

