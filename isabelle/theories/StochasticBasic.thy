theory StochasticBasic
  imports "HOL-Probability.Probability"
begin

section \<open>Basic Probability Facts\<close>

text \<open>
  Starter theory for the hybrid verification system.
  Imports HOL-Probability for measure-theoretic probability.
\<close>

lemma prob_space_measure_le_one:
  assumes "prob_space M"
  shows "emeasure M (space M) = 1"
  using assms by (simp add: prob_space.emeasure_space_1)

lemma prob_compl:
  assumes "prob_space M" "A \<in> events M"
  shows "prob M (space M - A) = 1 - prob M A"
  using assms by (simp add: prob_space.prob_compl)

end
