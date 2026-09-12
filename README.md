# Gap Entropy and Almost Instance-Wise Optimal Best-Arm Identification

This repository contains a Lean 4 formalization of the main results in
[Gap Entropy and Almost Instance-Wise Optimal Best-Arm Identification](docs/manuscript.pdf)
by [Jiarui Yao](https://maxwelljryao.github.io/), [Jiaxi Zhao](https://github.com/jiaxi98), and [Xiangxin Zhou](https://zhouxiangxin1998.github.io/). The manuscript resolves two
conjectures posed by Chen and Li in the COLT 2016 open problem
[Best Arm Identification: Almost Instance-Wise Optimality and the Gap Entropy Conjecture](https://proceedings.mlr.press/v49/chen16b.html),
for the Gaussian observation model below. Appendix I specifies the scope of the
formal verification and its relationship to the printed proofs.

## Setting and notation

We use the notation of Section 2 of the manuscript. An instance $I$ has $n \ge 2$
arms with independent unit-variance Gaussian rewards, means in $[0,1]$, and a
unique best arm. Let $\mu_{[r]}$ be the mean at rank $r$ in nonincreasing order,
and let $i_{[r]}$ be the label of the corresponding arm, breaking ties between
suboptimal arms by label. Thus $\mu_{[r]} = \mu_{i_{[r]}}$, and $i_{[1]}$ is the
best-arm label. Write
$\Delta_i = \mu_{[1]} - \mu_i$ for the gap of label $i$ and
$\Delta_{[r]} = \Delta_{i_{[r]}} = \mu_{[1]} - \mu_{[r]}$ for the gap at rank $r$. The instance
complexity and inverse squared smallest positive gap are

```math
H(I) = \sum_{r=2}^{n} \Delta_{[r]}^{-2},
\qquad D = \Delta_{[2]}^{-2}.
```

For integers $k \ge 0$, the dyadic gap groups and their complexities are

```math
\begin{aligned}
G_k &= \{i \ne i_{[1]} : 2^{-k} \le \Delta_i < 2^{-k+1}\}, \\
H_k &= \sum_{i \in G_k} \Delta_i^{-2},
\qquad p_k = H_k/H(I).
\end{aligned}
```

Since all means lie in $[0,1]$, the largest possible gap is $1$, and arms with
this gap belong to $G_0$. Gap entropy is the Shannon entropy of the normalized
group complexities; zero-mass groups are omitted:

```math
\mathrm{Ent}(I) = \sum_{k:p_k>0} p_k\log(1/p_k).
```

All unmarked logarithms are natural. As in equation (2.3), set

```math
L = \log(1/\delta),
```

```math
\ell(D) = \log\bigl(e + \log(e+D)\bigr).
```

For an algorithm $A$, let $T_A(I)$ be its unconditional expected number of samples,
including samples on erroneous or nonreturning trajectories. An algorithm is
$\delta$-correct if it returns the best label at some finite time with probability
at least $1-\delta$ on every admissible instance at every arm count.

For a label permutation $\pi \in S_n$, the instance $\pi I$ moves arm $i$ to label
$\pi(i)$. The order-oblivious instance-wise lower bound of equation (2.1) is

```math
\mathcal{L}(I,\delta) =
\inf_{A:\,A\text{ is }\delta\text{-correct}}
\frac{1}{n!}\sum_{\pi\in S_n} T_A(\pi I).
```

The infimum is taken separately at each target instance, but every competing
algorithm must remain correct on every admissible input. In Lean this quantity
is `GapEntropy.benchmark` in [Problem.lean](GapEntropy/Problem.lean).

## Main results

The following bounds hold for every admissible instance and every
$0 \lt  \delta \lt  1/10$. All constants are universal: they are independent of the
instance, arm count, and confidence level.

**Gap-entropy conjecture** (Theorem 2.1; Chen–Li Conjecture 3.5).

```math
\begin{aligned}
\mathcal{L}(I,\delta)
&\ge \tfrac15 H(I)\bigl[L+\mathrm{Ent}(I)\bigr], \\
\mathcal{L}(I,\delta)
&\le 6.4\cdot10^{13} H(I)\bigl[L+\mathrm{Ent}(I)\bigr].
\end{aligned}
```

For every globally $\delta$-correct algorithm, the lower bound holds for its
expected sample count averaged over all label permutations of the instance.
This is the weaker $1/5$ form of Theorem B.1 specified in Appendix I.
Declaration: `GapEntropy.gapEntropyConjecture` in
[GapEntropyTheorem.lean](GapEntropy/GapEntropyTheorem.lean).

**A single almost instance-wise optimal algorithm** (Theorem 2.2).
One algorithm family, receiving only $\delta$ and the arm count, is
$\delta$-correct, terminates almost surely, and has finite expected sample count
satisfying the following bound, with $H=H(I)$:

```math
T_A(I) \le C_{\mathrm{univ}}
\Bigl(H\bigl[L+\mathrm{Ent}(I)\bigr]+D\ell(D)\Bigr).
```

The algorithm receives no estimates of the gaps, $H(I)$, or $\mathrm{Ent}(I)$.
The formalization proves the bound with the explicit, unoptimized constant

```math
C_{\mathrm{univ}} = 12(10^{12}+1) = 12000000000012.
```

Declaration: `GapEntropy.universalEntropyUpperBound` in
[UniversalTheorem.lean](GapEntropy/UniversalTheorem.lean).

**Almost instance-wise optimality with a positive logarithmic convention**
(Section 2.3 and Appendix H.7; Chen–Li Conjecture 3.2).
The same algorithm satisfies

```math
T_A(I) = O\bigl(\mathcal{L}(I,\delta)+D\ell(D)\bigr).
```

The paper also uses the positive truncation, defined for $0\lt\Delta\lt1$ by

```math
g(\Delta) = \max\{1,\log\log(1/\Delta)\},
```

and at the endpoint by $g(1)=1$. The two conventions satisfy, on the entire
admissible gap range,

```math
g(\Delta) \le \ell(\Delta^{-2}) \le 7g(\Delta)
\qquad (0<\Delta\le1).
```

Thus the bound holds equivalently with $Dg(\Delta_{[2]})$ in place of $D\ell(D)$.
The declarations are `GapEntropy.almostInstanceWiseOptimality` and
`GapEntropy.positiveSourceAlmostInstanceWiseOptimality`; the comparison is proved
in [IteratedLogConvention.lean](GapEntropy/IteratedLogConvention.lean).

Corollary H.7 gives the source's untruncated two-arm term when
$0\lt \Delta_{[2]}\le e^{-e}$. For $e^{-e}\lt \Delta_{[2]}\le1$, the same algorithm has
cost $O(\mathcal{L}(I,\delta))$ alone; see
[GapRegimes.lean](GapEntropy/GapRegimes.lean). The literal untruncated source
statement on the entire gap range is recorded separately as
`GapEntropy.SourceConjecture32Literal` and is not proved: its logarithmic term is
negative near gap one and undefined at gap one in ordinary real analysis.

## Internal randomness and the scope of the algorithm model

The results of Appendix H are in `GapEntropy.PolicyRepresentations`:

- **Standard Borel internal randomness (H.1–H.3).** The order-oblivious
  instance-wise lower bound over arbitrary standard Borel probability spaces
  equals the Gaussian-seed lower bound. Declaration: `standardBenchmark_eq` in
  [StandardAlgorithms.lean](GapEntropy/PolicyRepresentations/StandardAlgorithms.lean).
- **Seed-independent upper-bound algorithms (H.4).** The two formal upper-bound
  witnesses admit measurable decision rules depending only on the observation
  history, and can use one-point seed spaces; see
  [DeterministicWitnesses.lean](GapEntropy/PolicyRepresentations/DeterministicWitnesses.lean).
- **Explicit abandonment (H.5).** Completion preserves sample cost and does not
  decrease success probability. Declaration: `explicitAbandonment_global_transport`
  in [AbandonmentTransport.lean](GapEntropy/PolicyRepresentations/AbandonmentTransport.lean).
- **History-dependent probability kernels (H.6).** Their implementation by
  Gaussian-seed algorithms preserves success probability, expected sample count,
  and almost-sure termination. Every globally correct kernel algorithm therefore
  satisfies the same permutation-averaged lower bound. Declaration:
  `KernelAlgorithm.benchmark_le_permutationAverage` in
  [KernelAlgorithms.lean](GapEntropy/PolicyRepresentations/KernelAlgorithms.lean).
  This is the comparison direction established in the paper; equality of the two
  infima over algorithm families is not claimed.

## Formal model and verification scope

A policy in [Model.lean](GapEntropy/Model.lean) is a measurable function of an
independent Gaussian seed and the finite observation history. It samples an arm
or returns a label; returned states are absorbing. The policy receives neither
the mean vector nor the best label. Rewards form an independent unit-variance
Gaussian table. Expected sample count is the unconditional nonnegative integral
in `ℝ≥0∞`; a path that never returns has infinite sample count.

The main theorems assume the stated instance and observation model and the
confidence range above. Concentration, change-of-measure, and execution bounds
are proved within the formalization. Almost-sure termination and finite
expectation are upper-bound conclusions, not separate admissibility assumptions.

Appendix I explains the deliberate differences from the printed proofs: the
formal lower bound uses permutation-averaged arm counts; the ever-flag argument
establishes the increasing-event Bernoulli domination needed by the proof; and
the formal algorithms use deterministic sample padding within each run. The
verified statements have the scope and explicit constants described there.

## Repository layout

| Path | Content |
| --- | --- |
| `GapEntropy/` | Instances, the Gaussian observation model, the lower bound (Appendix B), the algorithm with a fixed target instance (Appendix C), the single algorithm (Appendices D–F), and the main theorems. |
| `GapEntropy/PolicyRepresentations/` | The algorithm-model results of Appendix H: standard Borel internal randomness, history-dependent probability kernels, explicit abandonment, and seed-independent witnesses. |
| `Verification/` | Explicit transcriptions and checks of the main statements, expanded policy statements, and the recursive axiom audit. |
| `docs/manuscript.pdf` | The manuscript whose statements and numbering are referenced throughout. |
| `formalization.yaml` | Machine-readable project metadata and statement correspondence. |

## Building the formalization

The project uses Lean 4.33.1 and a pinned Mathlib revision. With
[elan](https://github.com/leanprover/elan) installed, fetch the Mathlib cache and
build the formalization and its verification modules:

```sh
lake exe cache get
lake build
```

[Verification/Statements.lean](Verification/Statements.lean) explicitly
transcribes correctness, unconditional cost, the permutation infimum, and the
four main statements, sharing the instance and operational-model definitions.
It imports the foundations but no main-result proof module.
[Verification/CheckStatements.lean](Verification/CheckStatements.lean) checks
these transcriptions against the proved declarations.
[Verification/PolicyStatements.lean](Verification/PolicyStatements.lean) checks
the expanded statements for the standard Borel formulation.

[Verification/AxiomAudit.lean](Verification/AxiomAudit.lean) recursively audits
the declarations in the main library and its policy supplement, including private
declarations. The audit rejects `sorryAx` and every axiom outside Lean's standard
classical base: `propext`, `Classical.choice`, and `Quot.sound`.

## Fresh-kernel replay

The reference checker shipped with the pinned Lean toolchain replays the complete
import closure in a fresh Lean kernel environment. The `Verification` entry
module imports the main library, the policy supplement, and the statement checks:

```sh
lake env leanchecker --fresh Verification
```

This uses Lean's reference kernel; it is separate from the original elaboration,
not a check by an independently implemented kernel. See the Lean reference on
[validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
