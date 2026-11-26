-- Prints the axioms of every theorem named in the paper. Run after `lake build`:
--   lake env lean scripts/Axioms.lean
-- Expected for each: propext, Classical.choice, Quot.sound (or a subset).
import Structural.Lever
import Structural.Arcs
import Structural.Certificate
import Structural.Spine
import Structural.Stepanov
import Applications.RHLogDeriv
import Applications.RHMellin
import Applications.RHPsi
import Solution
import Applications.StructuralWindow
#print axioms Structural.level_double_charge
#print axioms Structural.lifts_sq_le
#print axioms Structural.stepanov
#print axioms Structural.erdos_multiplicity_one
#print axioms Structural.level_stepanov
#print axioms Structural.auxiliary_size
#print axioms Structural.few_translates
#print axioms Structural.columns_fill_rows
#print axioms Structural.level_arcs
#print axioms Structural.level_charge_per_arc
#print axioms Structural.padicValNat_factorial_eq_sum_arcs
#print axioms Structural.primeError_eq_sum_excess_turns
#print axioms Structural.weight_nonneg
#print axioms Structural.centralBinom_arcs
#print axioms Structural.arc_eq_zero_of_lt_sq
#print axioms Structural.centralBinom_factorization_le_one
#print axioms Structural.certificate
#print axioms Structural.one_sided_bound
#print axioms Structural.no_zero_right_of_half
#print axioms Structural.zeros_on_line
#print axioms Structural.zeta_zeros_on_line
#print axioms RHStructure.logDerivZeta_bound_of_RH
#print axioms RHStructure.logDerivZeta_line_bound_of_RH
#print axioms RHStructure.mellin_smooth1_interp
#print axioms RHStructure.chebyshev_psi_of_RH
#print axioms Submission.chebyshev_psi_error
#print axioms Submission.exists_prime_in_short_interval
#print axioms StructuralWindow.gapCertificate_eventually_of_RH
#print axioms StructuralWindow.generalLaw_partial
#print axioms StructuralWindow.nextPrime_gap_of_RH
#print axioms StructuralWindow.march
