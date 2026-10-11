/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Traces, integral lattices and trace-dual bases in finite algebras

General facts used for the different estimates of tensor products of local fields
(IUT IV, Proposition 1.1):

* for a finite `ℚ_p`-algebra `A` in which the integral closure of `ℤ_p` is finitely generated,
  `A` is the localization of that integral closure, it has a `ℚ_p`-basis of integral elements in
  which integral elements have integral coordinates (`exists_basis_isIntegral`), and traces of
  integral elements lie in `ℤ_p` (`norm_trace_le_one_of_isIntegral`);
* the trace of an elementary tensor of a tensor product of finite free algebras is the product of
  the traces (`PiTensorProduct.trace_tprod`);
* in a semisimple commutative ring every ideal is cut out by an idempotent
  (`exists_mul_eq_zero_of_isSemisimpleRing`), and the trace of a finite algebra restricts to the
  trace of a surjective quotient on the corresponding factor (`trace_mul_eq_of_surjective`);
* the trace of `F ⊗_ℚ K` is the base change of the trace of `K`, and the trace-dual basis
  expansion holds after base change (`trace_one_tmul`, `sum_trace_smul_one_tmul`).
-/

namespace PadicLogVolume

open scoped TensorProduct

/-- A rational prime, as an element of `Nat.Primes`, is a prime (as an instance). -/
instance instFactPrimeNatPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### Lattices of integral elements in finite `ℚ_p`-algebras -/

section Lattice

variable (p : Nat.Primes) (A : Type*) [CommRing A] [Algebra ℚ_[p] A] [Algebra ℤ_[p] A]
  [IsScalarTower ℤ_[p] ℚ_[p] A] [Module.Finite ℚ_[p] A]

/-- A finite `ℚ_p`-algebra is the localization of the integral closure of `ℤ_p` in it at the
nonzero elements of `ℤ_p`. -/
theorem isLocalization_integralClosure :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ_[p] A)
      (nonZeroDivisors ℤ_[p])) A where
  map_units := by
    rintro ⟨_, r, hr, rfl⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] A]
    refine (IsUnit.mk0 _ ?_).map (algebraMap ℚ_[p] A)
    exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).mpr
      (nonZeroDivisors.ne_zero hr)
  surj z := by
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ_[p]) (Rₘ := ℚ_[p]) z (Algebra.IsIntegral.isIntegral z)
    refine ⟨(⟨m • z, hm⟩, ⟨algebraMap ℤ_[p] _ m, m, m.2, rfl⟩), ?_⟩
    change z * algebraMap (integralClosure ℤ_[p] A) A (algebraMap ℤ_[p] _ (m : ℤ_[p])) = m • z
    rw [← IsScalarTower.algebraMap_apply, Submonoid.smul_def, Algebra.smul_def, mul_comm]
  exists_of_eq {x y} h := ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact Subtype.ext h⟩

/-- **A `ℚ_p`-basis of a finite `ℚ_p`-algebra which is a `ℤ_p`-basis of the integral
closure of `ℤ_p`** (when the latter is a finitely generated `ℤ_p`-module): its vectors are
integral, and integral elements have coordinates in `ℤ_p`. -/
theorem exists_basis_isIntegral [Module.Finite ℤ_[p] (integralClosure ℤ_[p] A)] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ_[p] A), (∀ i, IsIntegral ℤ_[p] (b i)) ∧
      ∀ y : A, IsIntegral ℤ_[p] y → ∀ i, ‖b.repr y i‖ ≤ 1 := by
  haveI := isLocalization_integralClosure p A
  haveI : Module.IsTorsionFree ℤ_[p] A :=
    Module.IsTorsionFree.comap (S := ℚ_[p]) (algebraMap ℤ_[p] ℚ_[p])
      (fun r hr => by
        rw [isRegular_iff_ne_zero] at hr ⊢
        exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).mpr hr)
      (fun r m => algebraMap_smul ℚ_[p] r m)
  haveI : Module.IsTorsionFree ℤ_[p] (integralClosure ℤ_[p] A) :=
    Function.Injective.moduleIsTorsionFree (fun x : integralClosure ℤ_[p] A => (x : A))
      Subtype.val_injective fun _ _ => rfl
  obtain ⟨n, bC⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[p])
    (M := integralClosure ℤ_[p] A)
  refine ⟨n, bC.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) A, fun i => ?_,
    fun y hy i => ?_⟩
  · rw [Module.Basis.localizationLocalization_apply]
    exact (bC i).2
  · have : y = algebraMap (integralClosure ℤ_[p] A) A ⟨y, hy⟩ := rfl
    rw [this, Module.Basis.localizationLocalization_repr_algebraMap, PadicInt.algebraMap_apply,
      ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _

/-- **Traces of integral elements are integral**: for `x` integral over `ℤ_p` in a finite
`ℚ_p`-algebra in which the integral closure of `ℤ_p` is finitely generated,
`Tr(x) ∈ ℤ_p`. -/
theorem norm_trace_le_one_of_isIntegral [Module.Finite ℤ_[p] (integralClosure ℤ_[p] A)]
    {x : A} (hx : IsIntegral ℤ_[p] x) : ‖Algebra.trace ℚ_[p] A x‖ ≤ 1 := by
  classical
  obtain ⟨n, b, hb, hrepr⟩ := exists_basis_isIntegral p A
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  exact hrepr _ (hx.mul (hb i)) i

end Lattice

/-! ### The trace of an elementary tensor -/

/-- **The trace of an elementary tensor is the product of the traces**:
`Tr_{⊗ A_i / R}(⊗ y_i) = ∏ Tr_{A_i/R}(y_i)`, for finite free `R`-algebras `A_i`. -/
theorem PiTensorProduct.trace_tprod {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (y : ∀ i, A i) :
    Algebra.trace R (⨂[R] i, A i) (PiTensorProduct.tprod R y) =
      ∏ i, Algebra.trace R (A i) (y i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Basis.piTensorProduct b)]
  simp_rw [fun i => Algebra.trace_eq_matrix_trace (b i) (y i)]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Basis.piTensorProduct_apply, PiTensorProduct.tprod_mul_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  rfl

section Generic

variable {F A L : Type*} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
  [CommRing L] [Algebra F L] [Module.Finite F L]

omit [Module.Finite F A] in
/-- In a semisimple commutative ring every ideal `I` is annihilated by some `e` with
`1 - e ∈ I`. -/
theorem exists_mul_eq_zero_of_isSemisimpleRing [IsSemisimpleRing A] (I : Ideal A) :
    ∃ e : A, 1 - e ∈ I ∧ ∀ x ∈ I, e * x = 0 := by
  obtain ⟨J, hJ⟩ := exists_isCompl I
  have h1 : (1 : A) ∈ I ⊔ J := by rw [hJ.sup_eq_top]; trivial
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  refine ⟨j, by rw [← hij, add_sub_cancel_right]; exact hi, fun x hx => ?_⟩
  have hI : j * x ∈ I := I.mul_mem_left j hx
  have hJ' : j * x ∈ J := by rw [mul_comm]; exact J.smul_mem x hj
  exact (Submodule.disjoint_def.mp hJ.disjoint) _ hI hJ'

/-- If `Ψ : A → L` is surjective and `e` satisfies `Ψ e = 1`, `e·ker Ψ = 0`, then
`Tr_{A/F}(e·a) = Tr_{L/F}(Ψ a)`. -/
theorem trace_mul_eq_of_surjective (Ψ : A →ₐ[F] L) (hΨ : Function.Surjective Ψ) (e : A)
    (he1 : Ψ e = 1) (he : ∀ x, Ψ x = 0 → e * x = 0) (a : A) :
    Algebra.trace F A (e * a) = Algebra.trace F L (Ψ a) := by
  obtain ⟨σ, hσ⟩ := (Ψ.toLinearMap).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hΨ)
  have hσ' : ∀ z, Ψ (σ z) = z := fun z => LinearMap.congr_fun hσ z
  let s : L →ₗ[F] A := Algebra.lmul F A e ∘ₗ σ
  have hs : ∀ x, s (Ψ x) = e * x := by
    intro x
    have h0 := he (σ (Ψ x) - x) (by rw [map_sub, hσ', sub_self])
    rw [mul_sub, sub_eq_zero] at h0
    exact h0
  have h1 : Algebra.lmul F A (e * a) = s ∘ₗ (Ψ.toLinearMap ∘ₗ Algebra.lmul F A a) := by
    ext x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply', hs]
    ring
  have h2 : (Ψ.toLinearMap ∘ₗ Algebra.lmul F A a) ∘ₗ s = Algebra.lmul F L (Ψ a) := by
    ext z
    simp [s, he1, hσ']
  rw [Algebra.trace_apply, Algebra.trace_apply, h1, LinearMap.trace_comp_comm', h2]

end Generic

section BaseChange

variable {K : Type*} [Field K] [NumberField K] (F : Type*) [Field F] [Algebra ℚ F]

/-- `Tr_{F ⊗ K/F}(1 ⊗ x) = Tr_{K/ℚ}(x)`. -/
lemma trace_one_tmul (x : K) :
    Algebra.trace F (F ⊗[ℚ] K) (1 ⊗ₜ x) = algebraMap ℚ F (Algebra.trace ℚ K x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
    Algebra.trace_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)

/-- The trace-dual basis expansion `x = Σ_k Tr(x·b_k)·b^∨_k`. -/
lemma sum_trace_smul_traceDual (x : K) :
    ∑ k, Algebra.trace ℚ K (x * b k) • b.traceDual k = x := by
  conv_rhs => rw [← b.traceDual.sum_repr x]
  simp [Algebra.traceForm_apply]

/-- The trace-dual basis expansion on the base change `F ⊗_ℚ K`. -/
lemma sum_trace_smul_one_tmul (Y : F ⊗[ℚ] K) :
    ∑ k, Algebra.trace F (F ⊗[ℚ] K) (Y * (1 ⊗ₜ b k)) • ((1 : F) ⊗ₜ[ℚ] b.traceDual k) = Y := by
  induction Y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    have h : ∀ k, (r ⊗ₜ[ℚ] x) * (1 ⊗ₜ b k) = r • ((1 : F) ⊗ₜ[ℚ] (x * b k)) := by
      intro k
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    simp_rw [h, map_smul, trace_one_tmul, smul_eq_mul, mul_smul, algebraMap_smul,
      ← TensorProduct.tmul_smul, ← Finset.smul_sum, ← TensorProduct.tmul_sum,
      sum_trace_smul_traceDual, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add Y₁ Y₂ h₁ h₂ =>
    simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib, h₁, h₂]

end BaseChange

end PadicLogVolume
