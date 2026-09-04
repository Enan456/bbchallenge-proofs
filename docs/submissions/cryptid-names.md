# The Illinois Cryptid Bestiary of BB(6)

Each closed machine gets a name from Illinois cryptid folklore,
chosen to match its behaviour. Two names are inherited: **Antihydra**
(the community's), and **Dvisetu** (this program's own, given an
Illinois alias below). All eighteen are kernel-checked conditional
closures at axioms {propext, Quot.sound}.

| name | machine | folklore | behaviour it matches |
|---|---|---|---|
| Antihydra | (community) | (Greek) | guarded random walk, dies only if the head is severed |
| **Cohomo** | dossier-1 | Cole Hollow Road Monster (Pekin) | a tall thing built of stacked levels |
| **Piasa** | dossier-2 | the Piasa Bird (Alton bluffs) | a winged devourer with a spiral tail |
| **Grafton Piasa** | dossier-3 | the Piasa's mirror (Grafton, across the river) | the same beast, reflected |
| **Big Muddy** | rank-1 (dossier-5) | Big Muddy / Murphysboro Mud Monster | waves travelling through rising muck |
| **Dvisetu** (alias: Stump Pond Fish) | dossier-6 | the giant gar of Stump Pond (DuQuoin) | surfaces, collapses, regrows by thirds |
| **Kaskaskia** | dossier-7 | the Kaskaskia bell-devil | climbs a ladder rung by rung |
| **Cahokia** | dossier-8 | the mound-builders of Cahokia | stacks epochs into mounds |
| **Enfield** | dossier-9 | the Enfield Horror (three-legged leaper) | strikes in one direct spring |
| **Farmer City** | dossier-10 | the Farmer City Monster (glowing eyes) | a dense, thrashing digger |
| **Cairo** | dossier-11 | the creature of Cairo / Little Egypt | thrashes at the river confluence |
| **Mad Gasser** | dossier-12 | the Mad Gasser of Mattoon | changes its nature partway and vanishes |
| **Lawndale** | dossier-13 | the Lawndale Thunderbird | long glides between rare wingbeats |
| **Mazon Tully** | dossier-14 | Tully Monster (Illinois state fossil) | a two-ended body that grows at both ends |
| **Braidwood Tully** | dossier-15 | the twin specimen (Braidwood) | the same species, proven twice |
| **Coal City Tully** | dossier-16 | Mazon Creek locality | two-ended, right-favouring |
| **Pit Eleven Tully** | dossier-17 | Mazon Creek's famous Pit 11 | two-ended, left-favouring |
| **Essex Tully** | dossier-18 | Mazon Creek locality (Essex) | two-ended, the last of the beds |

---

## Cohomo (dossier-1)

**Folklore.** The Cole Hollow Road Monster, or "Cohomo," was
reported near Pekin in 1972: a tall, pale, foul-smelling figure that
witnesses described as looming.

**Why the name.** Cohomo's abstract state is a *stack of levels*, a
chain orbit that towers upward; the closure proof is a layered
endgame, halt localization stacked on an invariant discharged by
induction. It was the program's first original closure and the
template every later one was built on. Tall, foundational, built in
layers.

**Behaviour, plainly.** The machine records its progress as a growing
stack; the conjecture (the chain orbit never dies) is that the stack
never collapses to the halting configuration. Closed at 5,770 lines.

---

## Piasa and Grafton Piasa (dossier-2 and dossier-3)

**Folklore.** The Piasa Bird is Illinois's most famous monster, a
winged, antlered, spiral-tailed beast painted on the limestone
bluffs above Alton, said to have carried off those who passed below.
The mural faces the river; a mirror-image of it once faced from the
Grafton side.

**Why the name.** These two machines are a genuine mirror pair (one
law, reflected), so they are the Piasa and its reflection. Their
death cone is an exact Fibonacci tree branching at the golden ratio,
the spiral in the Piasa's tail. Halting is the devouring: a specific
control state reading a 0 with a 0 beside it, the probe event the
whole proof forbids.

**Behaviour, plainly.** The tape is a block of 1s with exactly two
holes; the machine walks the holes in a fixed gait and occasionally
reseeds five integers by a Euclid-and-Collatz renewal. The conjecture
is that the two counters never arrive almost-equal (the fatal
diagonal). The orbit grazes within distance 4 of death forever and
survives. Closed at 6,130 and 9,020 lines; validated against 10^9
raw steps each.

---

## Big Muddy (rank-1, dossier-5)

**Folklore.** The Big Muddy Monster (also the Murphysboro Mud
Monster) was sighted along the Big Muddy River in 1973: a white,
mud-caked thing that rose from the riverbank.

**Why the name.** Big Muddy's state is a *word that grows without
bound*, and its dynamics is a river of carries: 3-blocks travel in
wave trains through the muck, a deposited 2-block is a cursor riding
the current, and the frontier rule is a literal trisection, a wave
breaking into three. The rising water is the growing word.

**Behaviour, plainly.** A two-phase odometer on words. This was the
first closure on a state space of growing dimension, and it needed no
folded assumption: at cell grain the whole calculus is proven. The
conjecture is one clause, the word orbit never dies. Closed at 2,126
lines.

---

## Dvisetu, the Stump Pond Fish (dossier-6)

**Folklore.** Stump Pond in DuQuoin was long said to hold a monstrous
gar or catfish, surfacing and vanishing over decades. (Dvisetu,
Sanskrit for "two bridges," is the name this program gave it in July;
the fish is its Illinois alias.)

**Why the name.** The machine collapses its whole tape to a single
block (the fish diving), then a renewal regrows it, branched by
n mod 3, with a divide-by-3 branch that recurses (surfacing a third
of the size). Growth is 4/3 per cycle, a slow generalized-Collatz
climb.

**Behaviour, plainly.** One hole, two counters: the simplest state
geometry in the program. It carries the only folded assumption of the
eighteen (the divide renewal's raw faithfulness, honestly named
DivideFaithful). Closed at 1,942 lines, 36 hours after the dossier
opened.

---

## Kaskaskia and Cahokia (dossiers 7 and 8)

**Folklore.** Kaskaskia, Illinois's first capital, carries a legend
of a cursed bell and a devil that climbs; Cahokia, nearby, is the
site of the great prehistoric earthen mounds, built up in stages.

**Why the name.** Both machines carry a *unary ladder* `(10)^k` that
they climb rung by rung (Kaskaskia) and reload in stacked epochs
(Cahokia, whose state has an extra epoch counter g, the mounds
growing in layers). They are siblings with opposite ladder parity.

**Behaviour, plainly.** The macro state is a fixed integer vector
wearing an unbounded unary coat; drift drains the ladder, renewals
reload it at growth ~3/2. Closed at 1,036 and 1,037 lines; their
laws were validated 5,251/5,251 and 3,879/3,879 at 2x10^7 steps
before any Lean was written.

---

## Enfield (dossier-9)

**Folklore.** The Enfield Horror (1973, Enfield, Illinois) was a
grey, three-legged creature that reportedly sprang thirty feet in a
single bound.

**Why the name.** Enfield has the most direct halt anatomy of the
eighteen: the fatal probe *is* the halt (state B reading a 1), so it
strikes in one motion with no corridor to funnel through. A leaper,
not a stalker.

**Behaviour, plainly.** A one-sided word grower with very short
records (~22 raw steps each). It was the machine that proved the
raw-step engine needs no exact law, only a halt corridor and a record
definition, which opened the door to the whole final tranche. Closed
at 1,059 lines.

---

## Farmer City and Cairo (dossiers 10 and 11)

**Folklore.** The Farmer City Monster (1970) was a glowing-eyed,
hairy figure that haunted a campground; Cairo, at the confluence of
the Ohio and Mississippi in "Little Egypt," has its own river-beast
lore.

**Why the name.** Both are dense, thrashing zigzag machines whose
excursions nest in arithmetic families, the dip-aware pair. Farmer
City digs (dense dips); Cairo thrashes at a confluence (its probe
state is also its start state, the two meeting). Their laws were the
cleanest of any array-class machine (100.00% and 99.77% held-out),
yet the engine ignored the laws entirely and closed them from the
corridor alone.

**Behaviour, plainly.** One-sided growers with dense internal motion.
Closed at 1,061 and 1,067 lines; mirrors exact at 2x10^7 steps.

---

## Mad Gasser (dossier-12)

**Folklore.** The Mad Gasser of Mattoon (1944) was a phantom prowler
blamed for a wave of anesthetic attacks that changed pattern and then
stopped altogether, never identified.

**Why the name.** This machine *changes its nature partway*: near 13
million raw steps its power-header stack shifts regime, the counter
jumping from 1 to 404. Its mirror had to be validated across both
regimes to certify it. A creature that transforms mid-run and slips
away.

**Behaviour, plainly.** A right-growing machine that is
fixed-dimension only in the right alphabet (period-2 runs). Closed at
1,048 lines, with the mirror validated 7,197/7,197 across both sides
of the regime shift.

---

## Lawndale (dossier-13)

**Folklore.** In 1977 near Lawndale, Illinois, a giant bird (a
"thunderbird") reportedly lifted a boy briefly off the ground before
dropping him, gliding on enormous wings.

**Why the name.** Lawndale is a *glider*: its head turns only about
once every 250 steps, coasting in long straight runs between rare
reversals, exactly a bird's glide between wingbeats. Its feared long
record-gaps turned out to grow only linearly, so the standard fuel
sufficed.

**Behaviour, plainly.** A left-growing sparse-turn machine, ~31
counters in the right alphabet. Closed at 1,082 lines; mirror
10,909/10,909 at 2x10^7 steps, fuel margin 7,877x.

---

## The Tully Monsters (dossiers 14-18)

**Folklore.** *Tullimonstrum gregarium*, the Tully Monster, is the
official Illinois state fossil, found only in the Mazon Creek beds
(Braidwood, Coal City, Essex, and the famous Pit 11). It is a genuine
enigma: a soft-bodied animal with a segmented body, eye-stalks on one
side and a long clawed proboscis on the other. It grows and reaches
at *both ends*.

**Why the name.** These five machines are the *two-sided growers*:
their tape extends at both extremes, alternating, exactly the Tully's
two-ended body. They were long thought to need a bidirectional
segmenter; the raw-step engine closed all five from one side's
records alone, the far end absorbed by the engine's own mechanics.
Mazon and Braidwood are the twins: the same machine, table swapped,
so the same species certified twice.

**Behaviour, plainly.** Words growing at both ends, closed by
choosing records at the denser extreme (which has only two arrival
states, versus five or six on the sparse side). Closed at ~1,010
lines each; mirrors from 4,373 to 4,488 transitions exact at 2x10^7
steps, fuel margins ~1,900 to 3,000x. Dossiers 16/17/18 (Coal City,
Pit Eleven, Essex) complete the beds.
