# Etapa 12 — ponte para o subnível uniforme

Esta etapa começa a combinação dos passos 10 e 11 necessária para o
Lemma 3.5 do manuscrito. Os módulos intermediários são:

`MahlerLean/AnalyticLinearCombination.lean`

`MahlerLean/LocalJetPersistence.lean`

`MahlerLean/FiniteJetCover.lean`

## Resultado já formalizado

Para uma família analítica `φ : Fin N → ℝ → ℝ` e um vetor de
coeficientes `c`, define-se

`jetLinearCombo φ c x = ∑ j, c j * φ j x`.

O módulo prova:

- `analyticOnNhd_jetLinearCombo`: a combinação linear finita continua
  analítica;
- `iteratedDeriv_jetLinearCombo_eq_jetApply`: a derivada iterada de ordem
  `k` é exatamente a coordenada `jetApply` construída no passo 10;
- `analyticFamily_linearCombo_smooth`: a combinação possui todas as
  hipóteses de continuidade e diferenciabilidade exigidas pelo teorema
  `sublevel_measure_bound` do passo 11.

Esses resultados eliminam uma incompatibilidade formal entre a notação
matricial de jatos e a função escalar à qual se aplica a estimativa de
subnível.

O segundo módulo prova ainda:

- `exists_nhds_iteratedDeriv_abs_lower_bound`: uma coordenada de jato
  maior ou igual a `η` num ponto fornece a cota `η/2` para a mesma
  derivada numa vizinhança desse ponto;
- `exists_product_nhds_jetApply_abs_lower_bound`: a persistência vale
  quando variam simultaneamente o vetor de coeficientes e o ponto da
  fonte, relativamente ao produto com o compacto `K`;
- `exists_uniform_product_nhds_jetApply_lower_bound_of_analytic`: sob a
  não anulação do Wronskiano em `K`, existe um único `η > 0` válido para
  todos os coeficientes unitários e todos os pontos de `K`; apenas a
  ordem da derivada e a vizinhança podem variar.

O terceiro módulo completa a extração compacta:

- `jetApply_continuousAt_of_analytic`: cada coordenada do jato é
  conjuntamente contínua no vetor de coeficientes e no ponto da fonte;
- `exists_product_nhds_jetApply_abs_lower_bound_of_analytic`: a cota
  `η/2` vale numa vizinhança ambiente do par `(c,x)`;
- `exists_finite_uniform_jet_product_cover_of_analytic`: a esfera unitária
  de coeficientes vezes `K` admite uma subcobertura finita por patches;
  cada patch possui uma ordem `k` fixa, enquanto a mesma constante
  positiva `η` funciona em todos eles.

## O que ainda não está provado

Este commit intermediário não afirma o Lemma 3.5 completo. Ainda é
necessário formalizar:

1. a conversão da cobertura em uma partição finita adequada à
   aplicação repetida de `sublevel_measure_bound`;
2. a soma das estimativas locais com expoente uniforme `1/(N-1)`;
3. a representação do subnível como união de um número uniformemente
   limitado de intervalos;
4. a especialização à família racional `x^i f(x)^j`, que dará o
   Corolário 3.6.

Nenhuma dessas conclusões pendentes é introduzida como axioma ou
placeholder. Todos os teoremas são verificados pelo build e pela auditoria
automática de axiomas.
