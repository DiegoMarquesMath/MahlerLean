# Etapa 12 — ponte para o subnível uniforme

Esta etapa começa a combinação dos passos 10 e 11 necessária para o
Lemma 3.5 do manuscrito. O módulo intermediário é:

`MahlerLean/AnalyticLinearCombination.lean`

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

## O que ainda não está provado

Este commit intermediário não afirma o Lemma 3.5 completo. Ainda é
necessário formalizar:

1. a escolha local de uma ordem de derivada `k` em cada ponto `(c,x)` da
   esfera de coeficientes vezes o intervalo;
2. a persistência do lower bound do jato em uma vizinhança produto;
3. a extração de uma subcobertura finita independente de `c`;
4. a soma das estimativas locais com expoente uniforme `1/(N-1)`;
5. a representação do subnível como união de um número uniformemente
   limitado de intervalos;
6. a especialização à família racional `x^i f(x)^j`, que dará o
   Corolário 3.6.

Nenhuma dessas conclusões pendentes é introduzida como axioma ou
placeholder. Os três teoremas deste módulo foram compilados previamente
com `warningAsError=true` e serão novamente verificados pelo build e pela
