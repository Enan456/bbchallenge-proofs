# Annotated bibliography, DeepMath 2026 submission (v10)

Direct quotes are verbatim from the cited source (arXiv abstract,
published abstract, or the source's own page, as noted). Two entries
carry no quote because their publisher pages are access-controlled;
nothing is quoted that was not retrieved.

## Busy beaver and deciders

**The bbchallenge Collaboration. Determination of the fifth Busy
Beaver value. arXiv:2509.12337.**
Quote: "We prove that $S(5) = 47{,}176{,}870$ using the Coq proof
assistant." And: "Our result marks the first determination of a new
Busy Beaver value in over 40 years and the first Busy Beaver value
ever to be formally verified."
Relevance: the direct predecessor of our program; establishes the
standard of kernel-checked busy beaver results that our Lean
developments follow, and the collaboration whose BB(6) holdout set
our census classifies.

**The bbchallenge Collaboration. Turing machine deciders, part I.
arXiv:2504.20563.**
Quote: "To do so, we write deciders: programs that take as input a
Turing machine and output either HALT, NONHALT, or UNKNOWN." And:
"Each decider is specialised in recognising a particular type of
non-halting behavior."
Relevance: defines the decider paradigm whose UNKNOWN residue at six
states is exactly our 1,094-machine cohort; our per-machine
certifications are the complementary, non-automated regime.

**P. Michel. The Busy Beaver Competition: a historical survey.
arXiv:0906.3749.**
Quote: "Tibor Rado defined the Busy Beaver Competition in 1962." And:
"He used Turing machines to give explicit definitions for some
functions that are not computable and grow faster than any computable
function."
Relevance: the standard historical reference; documents that
champion machines have long been observed to simulate Collatz-like
iterations, the phenomenon our machines exhibit and we certify.

**S. Aaronson. The Busy Beaver Frontier. SIGACT News 51(3), 2020.**
Quote: "The Busy Beaver function, with its incomprehensibly rapid
growth, has captivated generations of computer scientists,
mathematicians, and hobbyists." And: "In my opinion, the BB function
makes the concepts of computability and uncomputability more vivid
than anything else ever invented."
Relevance: frames the open-problem landscape our submission addresses
for a general mathematical audience and argues the field's
significance in terms the conference audience shares.

## Collatz-type arithmetic

**T. Tao. Almost all orbits of the Collatz map attain almost bounded
values. arXiv:1909.03562.**
Quote: "In this paper we show that for any function $f$ on the
positive integers with $\lim f(N) = +\infty$, one has
$\mathrm{Col}_{\min}(N) \le f(N)$ for almost all $N$."
Relevance: the strongest known result for the class of maps our
machines implement; our almost-all-seeds measurement for the renewal
map $R$ is the empirical shadow of this theorem's shape, and the
missing tail-hazard bound we identify is an invariant-measure
argument of this kind.

## Turing machines as dynamical systems

**C. Moore. Generalized shifts: unpredictability and undecidability
in dynamical systems. Nonlinearity 4 (1991).**
Quote: "These systems possess a type of unpredictability
qualitatively stronger than that which has been previously discussed
in the study of low-dimensional chaos, and many simple questions
about their dynamics are undecidable."
Relevance: the founding statement of the machine-as-dynamical-system
view that our coordinate-chart methodology operationalizes.

**P. Kůrka. On topological dynamics of Turing machines. Theoretical
Computer Science 174 (1997).** (No quote: publisher page is
access-controlled.)
Relevance: develops the topological-dynamics formalism for Turing
machines (moving-head and moving-tape models) on which the modern
study of machine trajectories rests.

## The coordinate charts

**O. Viro. Dequantization of real algebraic geometry on logarithmic
paper. arXiv:math/0005163.**
Quote: "On logarithmic paper some real algebraic curves look like
smoothed broken lines." And: "The corresponding deformation can be
viewed as a quantization, in which the broken line is a classical
object and the curves are quantum."
Relevance: the source of our logarithmic chart's meaning: the
piecewise-linear regimes we observe are the tropical (classical)
limit of the machine's arithmetic, which is why log coordinates
straighten them.

**G. Litvinov. The Maslov dequantization, idempotent and tropical
mathematics: a brief introduction. arXiv:math/0507014.**
Quote: "Tropical mathematics can be treated as a result of the
so-called Maslov dequantization of the traditional mathematics over
numerical fields as the Planck constant $\hbar$ tends to zero taking
imaginary values."
Relevance: names the dequantization limit precisely; grounds the
paper's statement that our quantum-inspired toolkit borrows a
discipline, not a metaphor.

**M. Nickel, D. Kiela. Poincaré embeddings for learning hierarchical
representations. NeurIPS 2017.**
Quote: "Due to the underlying hyperbolic geometry, this allows us to
learn parsimonious representations of symbolic data by simultaneously
capturing hierarchy and similarity."
Relevance: the machine-learning precedent for our hyperbolic chart:
nested renewal generations are hierarchical data, and they separate
in the Poincaré disk for the same reason.

**C. Series. The modular surface and continued fractions. J. London
Math. Soc. 31 (1985).** (No quote: publisher page is
access-controlled.)
Relevance: the geodesic-coding dictionary we invoke when restating
the five-integer conjecture as horoball avoidance on the modular
surface.

## Verification and interactive proofs

**Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen.
MIP* = RE. arXiv:2001.04383.**
Quote: "We show that the class MIP* of languages that can be decided
by a classical verifier interacting with multiple all-powerful
quantum provers sharing entanglement is equal to the class RE of
recursively enumerable languages." And: "An immediate byproduct of
our result is that there is an efficient reduction from the Halting
Problem to the problem of deciding whether a two-player nonlocal game
has entangled value 1 or at most 1/2."
Relevance: the proven endpoint of our verification spectrum; the
byproduct sentence is the exact bridge from halting problems to
verifiable games that motivates our two-prover census harness.

**H. Mousavi, S. Nezhadi, H. Yuen. Nonlocal games, compression
theorems, and the arithmetical hierarchy. STOC 2022;
arXiv:2110.04651.**
Quote: "We prove that deciding whether the quantum value of a
two-player nonlocal game is exactly equal to 1 is complete for
$\Pi_2$."
Relevance: places non-halting claims (our $\Pi_1$ statements) within
reach of the zero-gap entangled-prover frame, which is why the
spectrum's top rung covers the busy beaver program's claim class.

## The collaborative-verification pattern

**T. Tao et al. The Equational Theories Project: advancing
collaborative mathematical research at scale. arXiv:2512.07087.**
Quote: "The project successfully determined all 22 028 942 edges of
the implication graph between the 4694 simplest equational laws on
magmas."
Relevance: the flagship instance of the human-AI-kernel workflow our
project follows: machine-scale case coverage arbitrated by a proof
kernel with humans owning the claims.

**Palomar: a registry of Lean-verified mathematics.
palomar-registry.org.**
Quote (from the registry's own description): "Palomar records
mathematical claims from fixed versions of their source files, checks
their proofs with Lean, and publishes the exact statement, the
libraries it uses, and the review's comments."
Relevance: the publication channel where our certified reductions are
registered, making the paper's Lean claims externally checkable at a
pinned commit.
