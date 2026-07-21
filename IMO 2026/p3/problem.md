# IMO 2026 Problem 3

**Day 1 · Combinatorics / game theory**

Let $n$ be a positive integer. Liu Bang and Xiang Yu have a stick of length $1$
and want to divide it between themselves. Liu marks at most $n$ points on the
stick, and then Xiang marks at most $n$ points on the stick. The marked points
are distinct. Then, the stick is cut at all marked points, creating a number of
pieces. Afterwards, they take turns claiming any unclaimed piece of the stick,
with Liu going first. Each player's goal is to maximise the total length of
their own pieces.

For each $n$, determine the largest value $c$ such that Liu may guarantee a
total length of at least $c$, regardless of Xiang's play.

---

Transcription notes:

- Liu marks first (up to $n$ points), then Xiang marks (up to $n$ points) with
  full knowledge of Liu's marks; all marks are distinct.
- Piece-claiming alternates starting with Liu; any unclaimed piece may be taken
  on a turn. The answer $c$ is a function of $n$.
