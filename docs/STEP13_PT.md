# Etapa 13 — determinantes com duas alturas

A etapa formaliza o argumento determinantal que converte muitos pontos
racionais próximos do gráfico em uma relação polinomial. O desenvolvimento
está na branch `step13-determinants`.

## Limite inferior aritmético

O módulo `TargetLinearDeterminant.lean` considera a matriz dos monômios

```text
1, y, x, xy, ..., x^d, x^d y
```

de dimensão (N=2(d+1)). Multiplicar a linha (k) por (q_k^d b_k)
produz uma matriz inteira. Se o determinante não se anula,

```text
|det M| ≥ 1 / ∏ₖ (qₖ^d bₖ).
```

Para (q_k≤2Q) e (b_k≤2B), as duas alturas permanecem separadas:

```text
|det M| ≥ 1 / ((2Q)^(dN) (2B)^N).
```

As frações não precisam estar reduzidas, os numeradores podem ter qualquer
sinal e o caso (d=0) está incluído. O teorema
`targetLinearMatrix_det_eq_zero_of_lt` transforma uma cota analítica
estritamente menor que esse limiar em `det M = 0`.

## Taylor e a potência triangular

Os módulos `CurveTaylorBounds.lean` e
`TargetLinearCurveTaylor.lean` fornecem Taylor vetorial uniforme e sua
especialização à curva

[
Phi_d(x)=(1,f(x),x,xf(x),ldots,x^d,x^df(x)).
]

O resto tem a forma (Cρ^S) em qualquer ordem positiva (S) permitida
pela regularidade analítica.

`SmoothCurveDeterminant.lean` fatoriza a matriz das linhas polinomiais de
Taylor em uma matriz de coeficientes escalares e uma matriz de derivadas.
`AlternatingTaylorExpansion.lean` dá a versão geral:

- expande o determinante por multilinearidade;
- elimina escolhas não injetivas de ordens de derivada;
- prova que (N) ordens distintas somam pelo menos (N(N-1)/2);
- obtém diretamente o fator (ρ^{N(N-1)/2});
- constrói automaticamente uma constante finita a partir dos determinantes
  das linhas de derivadas.

## Perturbações e restos

`DeterminantAnalyticBounds.lean` prova as cotas de Leibniz pelas normas L¹
das linhas, identifica exatamente a perturbação vertical e controla o termo
em que todas as linhas são erros.

`DeterminantRowExpansion.lean` formaliza a expansão completa de
(det(P+R)) por escolhas independentes entre linha principal e linha de
resto. Se uma linha do resto tem tamanho (E) e todas as linhas têm tamanho
no máximo (B), cada termo misto satisfaz

[
|det M_{m misto}|
 le #operatorname{Perm}(N),E,B^{N-1}.
]

A identidade de expoentes usada na perturbação vertical também está provada:

[
rN+rac{(N-r)(N-r-1)}2
 =rac{N(N-1)}2+rac{r(r+1)}2.
]

## O que falta

A combinatória determinantal e a potência triangular já estão formalizadas.
O próximo elo é montar, num único teorema uniforme, as constantes de norma
das linhas, o resto vetorial de Taylor e a expansão `P+R`. Depois disso
ainda será necessário:

1. especializar a cota completa à curva alvo-linear;
2. incorporar simultaneamente os erros verticais (y_k-f(x_k));
3. comparar o limite superior com o limite inferior de duas alturas;
4. aplicar o anulamento aos menores máximos, normalizar a relação e integrar
   o resultado à contagem da Proposição 5.1.

A etapa 13 e a Proposição 5.1 ainda não estão concluídas.

## Verificação

O commit `8034de7890ad557f2f69037a19afd6ab566626ee` passou no
[GitHub Actions run 35490297130](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35490297130).

- build integral: 3142 jobs;
- avisos tratados como erros;
- 224 declarações inspecionadas por `scripts/Audit.lean`;
- dependências axiomáticas impressas limitadas a
  `propext`, `Classical.choice` e `Quot.sound`;
- nenhum `sorryAx` ou axioma próprio do projeto.
