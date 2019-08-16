Theorem ch3 :
forall P Q I O : Prop,
  (P -> I) ->
  (Q -> O) ->
  ((I /\ O) -> False) ->
  P ->
  ~Q.
(*

前提

  P:詠彦くんは午前六時にイリナちゃんと館内にいた。
  Q:周防さんが午前六時にイリナちゃんが館外を歩くのを見た。
  I:イリナちゃんは午前六時に館内にいた。
  O:イリナちゃんは午前六時に館外にいた。

  P -> I:
    詠彦くんは午前六時にイリナちゃんと館内にいた　ならば
    イリナちゃんは午前六時に館内にいた。

  Q -> Q
    周防さんが午前六時にイリナちゃんが館外を歩くのを見た　ならば
    イリナちゃんは午前六時に館外にいた。

  (I /\ O) -> False:
    イリナちゃんは午前六時に館内にいた　かつ　イリナちゃんは午前六時に館外にいた　ならば
    矛盾である。

  P:
    詠彦くんは午前六時にイリナちゃんと館内にいた。

結論

  ~Q:周防さんの証言が偽だった。

*)
Proof.
  intros P Q I O A1 A2 A3 A4.
  intro.
  apply A3.
  split.
  -
    apply A1.
    apply A4.
  -
    apply A2.
    apply H.
Qed.

From mathcomp
Require Import ssreflect.

Theorem ch3_ssr :
forall P Q I O : Prop,
  (P -> I) ->
  (Q -> O) ->
  ((I /\ O) -> False) ->
  P ->
  ~Q.
Proof.
  move=> P Q I O A1 A2 A3 A4.
  rewrite /not.
  move=> Q_is_true.
  apply: A3.
  split.
  -
    apply: A1.
    done.
  -
    apply: A2.
    done.
Qed.
