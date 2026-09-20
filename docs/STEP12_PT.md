# Etapa 12 — ponte para o subnível uniforme

Esta etapa começa a combinação dos passos 10 e 11 necessária para o
Lemma 3.5 do manuscrito. Os módulos intermediários são:

`MahlerLean/AnalyticLinearCombination.lean`

`MahlerLean/LocalJetPersistence.lean`

`MahlerLean/FiniteJetCover.lean`

`MahlerLean/LocalUniformSublevel.lean`

`MahlerLean/FiniteSublevelAssembly.lean`

`MahlerLean/UniformIntervalCover.lean`

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

O quarto módulo faz a primeira aplicação local efetiva da estimativa de
subnível:

- `sublevel_set_eq_empty_of_abs_lower_bound` e
  `sublevel_measure_eq_zero_of_abs_lower_bound`: uma cota absoluta
  estrita exclui o subnível menor, tratando separadamente a ordem zero;
- `jetLinearCombo_sublevel_measure_bound`: para uma ordem positiva fixa
  num intervalo, aplica a estimativa explícita do passo 11 à combinação
  linear analítica;
- `jetLinearCombo_local_sublevel_control`: reúne os casos de ordem zero
  e ordem positiva numa dicotomia local pronta para a montagem finita.

O quinto módulo realiza a montagem quantitativa para uma cobertura por
intervalos:

- `rpow_inv_nat_le_rpow_inv_nat`: para uma base em `[0,1]`, permite
  substituir os expoentes variáveis `1/k` pelo expoente comum
  `1/(N-1)`;
- `measureReal_le_card_mul_of_finite_cover`: soma estimativas locais
  sobre uma cobertura finita;
- `jetLinearCombo_sublevel_measure_bound_of_finite_interval_cover`:
  combina os dois fatos anteriores com a estimativa local da etapa 12d,
  permitindo que a ordem positiva da derivada varie entre os intervalos.

O sexto módulo completa a extração topológica dos intervalos:

- `exists_product_nhds_Icc_subset`: dentro de uma vizinhança de um par
  coeficiente/fonte, escolhe uma vizinhança dos coeficientes e um
  intervalo compacto da fonte contido no domínio analítico;
- `exists_finite_uniform_jet_interval_cover_of_analytic`: aplica essa
  construção a todos os pares normalizados e usa compactidade para obter
  uma única família finita de retângulos; cada retângulo possui ordem de
  derivação fixa e a mesma cota positiva de jato.

## O que ainda não está provado

Esta etapa intermediária ainda não afirma o Lemma 3.5 completo. Ainda é
necessário formalizar:

1. recortar os intervalos extraídos pelo intervalo-fonte `J` e
   alimentar a família resultante no teorema de montagem, incluindo os
   patches de ordem zero;
2. obter assim a afirmação global de medida sem hipóteses auxiliares de
   cobertura;
3. representar o subnível como união de um número uniformemente limitado
   de intervalos;
4. especializar o resultado global à família racional `x^i f(x)^j`,
   obtendo o Corolário 3.6.

Nenhuma dessas conclusões pendentes é introduzida como axioma ou
placeholder. Todos os teoremas são verificados pelo build e pela auditoria
automática de axiomas.
