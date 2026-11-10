module

public import LeanML

@[expose] public section

set_option autoImplicit false
#print axioms LeanML.Optimization.descent_lemma
#print axioms LeanML.Optimization.gradient_descent_step_decreases
#print axioms LeanML.Optimization.gradientDescent_rate
#print axioms LeanML.Representation.attention_permute
#print axioms LeanML.Representation.selfAttention_permute
#print axioms LeanML.Information.shannonEntropy_nonneg
#print axioms LeanML.Information.shannonEntropy_le_log_card
#print axioms LeanML.Information.klDivergence_eq_zero_iff
#print axioms LeanML.Information.dataProcessing_kernel
#print axioms LeanML.LearningTheory.hoeffding_sum
#print axioms LeanML.LearningTheory.sauerShelah
#print axioms LeanML.Generative.finiteELBO_le_logEvidence
#print axioms LeanML.Representation.matrixSelfAttention_permute
#print axioms LeanML.Optimization.gradientDescent_linear_rate
#print axioms LeanML.Optimization.gradientDescent_convex_rate
#print axioms LeanML.Optimization.DifferentiableNode.reverse_correct
#print axioms LeanML.LearningTheory.finiteClass_erm_bound
#print axioms LeanML.LearningTheory.hoeffding_bounded_sum
#print axioms LeanML.Information.shannonEntropy_uniform
#print axioms LeanML.Optimization.DifferentiableNode.reverse_fork
#print axioms LeanML.LearningTheory.hoeffding_bounded_mean
#print axioms LeanML.LearningTheory.extendedVCDimension_mono
