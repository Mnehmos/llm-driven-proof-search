# IMO 2026 Problem 4

**Day 2 · Geometry / game theory**

Shan-Yu and Mulan are playing a game. Let $\theta$ be an angle with
$0^\circ < \theta < 180^\circ$ known to both players. Initially, Shan-Yu makes
a paper triangle $\mathcal{T}$ with measurements of his choice. Then, they
repeatedly perform the following steps:

- If $\mathcal{T}$ has at least one angle measuring exactly $\theta$, then the
  game stops and Mulan wins.
- Otherwise, Mulan chooses a point $P$ on the perimeter of $\mathcal{T}$,
  different from its three vertices. She then makes a straight cut from $P$ to
  the opposite vertex of $\mathcal{T}$, splitting it into two triangles.
- Shan-Yu discards one of the two triangles. The remaining triangle becomes the
  new $\mathcal{T}$.

For which real values of $\theta$ can Mulan guarantee her victory in finitely
many steps, no matter how Shan-Yu plays?

---

Transcription notes:

- $P$ lies in the interior of one of the three sides; "the opposite vertex" is
  the vertex not on that side, so every cut is a cevian and both resulting
  pieces are triangles.
- Shan-Yu picks the initial triangle *after* $\theta$ is known, and chooses
  which piece survives each cut. $\theta$ ranges over all reals in
  $(0^\circ, 180^\circ)$, not just rational or integer degree values.
