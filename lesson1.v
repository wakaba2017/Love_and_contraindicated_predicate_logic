Theorem ch1 :
forall P Q R S T U V : Prop,
  P ->
  Q ->
  R ->
  ((P /\ Q) -> S) ->
  (S -> T) ->
  ((T /\ R) -> U) ->
  (U -> V) ->
  V.
(*

前提

  P:被害者は妊娠している。
  Q:スターアニスは子宮緊縮作用を持つ。
  R:被害者にしきみの実を食べさせた。
  S:被害者はスターアニスを食べれば流産する。
  T:被害者にしきみの実を食べさせる必要がない。
  U:必要のない行為を行った。
  V:行為は故意ではない。

  (P /\ Q) -> S:
    被害者は妊娠している　かつ　スターアニスは子宮緊縮作用をもつ　ならば
    被害者はスターアニスを食べれば流産する。

  S -> T:
    被害者はスターアニスを食べれば流産する　ならば
    被害者にしきみの実を食べさせる必要がない。

  (T /\ R) -> U:
    被害者にしきみの実を食べさせる必要がない　かつ　被害者にしきみの実を食べさせた　ならば
    必要のない行為を行った。

  U -> V
    必要のない行為を行った　ならば　行為は故意ではない。

結論

  V:行為は故意ではない。

*)
Proof.
  intros P Q R S T U V A1 A2 A3 A4 A5 A6 A7.
  apply A7.
  apply A6.
  split.
  - (* Tが成立することの証明 *)
    apply A5.
    apply A4.
    split.
    + (* Pが成立することの証明 *)
      apply A1.
    + (* Qが成立することの証明 *)
      apply A2.
  - (* Rが成立することの証明 *)
    apply A3.
Qed.

From mathcomp
Require Import ssreflect.

Theorem ch1_ssr :
forall P Q R S T U V : Prop,
  P ->
  Q ->
  R ->
  ((P /\ Q) -> S) ->
  (S -> T) ->
  ((T /\ R) -> U) ->
  (U -> V) ->
  V.
Proof.
  move=> P Q R S T U V A1 A2 A3 A4 A5 A6 A7.
  apply: A7.
  apply: A6.
  split.
  - (* Tが成立することの証明 *)
    apply: A5.
    apply: A4.
    split.
    + (* Pが成立することの証明 *)
      done.
    + (* Qが成立することの証明 *)
      done.
  - (* Rが成立することの証明 *)
    done.
Qed.

