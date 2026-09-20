# Etapa 13 — determinantes com duas alturas

A etapa formaliza o argumento determinantal usado para converter muitos pontos
racionais próximos do gráfico em uma relação polinomial. O trabalho está na
branch `step13-determinants`.

## Parte aritmética concluída

O módulo `TargetLinearDeterminant.lean` considera a matriz de monômios

```text
1, y, x, xy, ..., x^d, x^d y
```

de dimensão (N=2(d+1)). Multiplicar a linha (k) por
(q_k^d b_k) produz uma matriz inteira. Portanto, se o determinante não se
anula,

```text
|det M| ≥ 1 / ∏ₖ (qₖ^d bₖ).
```

Para (q_k≤2Q) e (b_k≤2B), obtemos separadamente as duas alturas:

```text
|det M| ≥ 1 / ((2Q)^(dN) (2B)^N).
```

As frações não precisam estar reduzidas, os numeradores podem ter qualquer
sinal e o caso (d=0) está incluído. O teorema
`targetLinearMatrix_det_eq_zero_of_lt` compara uma cota analítica estrita
com esse limiar e conclui `det M = 0`.

## Parte analítica formalizada

Três módulos fornecem agora a infraestrutura do limite superior:

- `DeterminantAnalyticBounds.lean`: desigualdade de Leibniz pelas normas
  L¹ das linhas, coordenadas exatas da perturbação vertical e cotas uniformes;
- `CurveTaylorBounds.lean`: Taylor vetorial em intervalo compacto, constante
  não negativa e resto uniforme (Cρ^N);
- `TargetLinearCurveTaylor.lean`: especialização à curva
  (Phi_d(x)=(1,f(x),x,xf(x),…,x^d,x^df(x))).

Também está provada a decomposição exata

```text
targetLinearMatrix = graphMatrix + perturbationMatrix
```

e a cota do termo extremo em que todas as linhas são perturbações. A
identidade de expoentes da expansão é

```text
rN + (N-r)(N-r-1)/2
  = N(N-1)/2 + r(r+1)/2.
```

## Estado da prova

O marco atual conclui a limpeza aritmética de denominadores e os dados de
Taylor necessários ao lema analítico. Ainda faltam:

1. expandir o determinante por multilinearidade para qualquer subconjunto de
   linhas perturbadas;
2. provar que as linhas de Taylor restantes fornecem o fator
   (ρ^{(N-r)(N-r-1)/2});
3. combinar as cotas e obter o decaimento total
   (ρ^{N(N-1)/2});
4. aplicar o resultado aos menores máximos, normalizar a relação e integrá-la
   à contagem da Proposição 5.1.

Assim, a etapa 13 e a Proposição 5.1 ainda não estão concluídas.

## Verificação

O commit `953661b05f47ca3d3645b1ce1b0c72fc149bd031` passou no
[GitHub Actions run 35488804840](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35488804840).

- build integral: 3139 jobs;
- avisos tratados como erros;
- 208 declarações inspecionadas por `scripts/Audit.lean`;
- dependências axiomáticas impressas limitadas a
  `propext`, `Classical.choice` e `Quot.sound`;
- nenhum `sorryAx` ou axioma próprio do projeto.
