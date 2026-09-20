# Etapa 13 — determinantes com duas alturas

## Bloco aritmético

`TargetLinearDeterminant.lean` trata o limite inferior do determinante
da matriz de monômios `1, y, x, xy, ..., x^d, x^d y`, com N = 2(d+1).
Os numeradores podem ser quaisquer inteiros; os denominadores são naturais
positivos. As frações não precisam estar reduzidas.

Multiplicar a linha k por q_k^d b_k produz uma matriz inteira. O módulo
de um determinante inteiro não nulo é pelo menos 1. Consequentemente,

```text
|det M| ≥ 1 / ∏_k (q_k^d b_k).
```

Se q_k ≤ 2Q e b_k ≤ 2B, segue a forma de duas alturas

```text
|det M| ≥ 1 / ((2Q)^(dN) (2B)^N).
```

A hipótese não estrita nos denominadores é ligeiramente mais geral que
a do manuscrito. Os expoentes dN e N são conservados separadamente.
O caso d=0 está incluído.

## Interface com a estimativa analítica

`targetLinearMatrix_det_eq_zero_of_lt` prova que uma estimativa estrita
abaixo desse limiar força det M = 0. A estimativa analítica permanece uma
hipótese explícita nesse teorema; ela não foi substituída por um axioma.

## Bloco analítico preparatório

`DeterminantAnalyticBounds.lean` formaliza a desigualdade de Leibniz em
termos da norma L¹ de cada linha. Também identifica exatamente a diferença
entre as linhas `Ψ_d(x,y)` e `Ψ_d(x,z)`: as coordenadas pares anulam-se
e as ímpares são `x^i (y-z)`. Disso resulta o controle uniforme

```text
‖E_k‖₁ ≤ 2(d+1) X^d δ.
```

A identidade de expoentes usada na expansão perturbada também foi provada:

```text
rN + (N-r)(N-r-1)/2 = N(N-1)/2 + r(r+1)/2.
```

Este bloco fornece as estimativas elementares que entram no Lema do
determinante perturbado. Ele ainda não formaliza a expansão completa por
multilinearidade nem o decaimento de Taylor da curva suave.

## Próximos blocos

1. Decaimento de determinantes ao longo de uma curva suave, com expoente N(N−1)/2.
2. Montagem da expansão multilinear com as linhas de perturbação.
3. Aplicação a todos os menores máximos e extração de uma relação com
   coeficientes normalizados.
4. Integração com os subníveis e a contagem da Proposição 5.1.

Este bloco conclui o lema aritmético de limpeza de denominadores.
Não conclui toda a etapa de determinantes nem a Proposição 5.1.

## Verificação

As seis declarações aritméticas e as oito declarações analíticas novas estão
incluídas em `scripts/Audit.lean`. O commit `8ebbe3f` passou no
[GitHub Actions run 35487464974](https://github.com/DiegoMarquesMath/MahlerLean/actions/runs/35487464974):
compilação integral, avisos tratados como erros e inspeção das dependências
axiomáticas.

## Infraestrutura analítica

O módulo `DeterminantAnalyticBounds` introduz a norma L¹ de cada linha e
prova, diretamente pela fórmula de Leibniz, uma cota para o determinante
pela soma sobre permutações dos produtos dessas normas. Uma versão uniforme
dá o fator finito `#Perm(N) K^N`.

Para a família alvo-linear, a perturbação da linha entre `(x,y)` e
`(x,z)` é identificada coordenada a coordenada: as coordenadas pares
desaparecem e as ímpares são `x^i(y-z)`. Em um intervalo `|x|≤X`,
`X≥1`, isso fornece uma cota L¹ uniforme proporcional a `X^d |y-z|`.

Também foram formalizadas a identidade e a desigualdade de expoentes
`rN+(N-r)(N-r-1)/2 ≥ N(N-1)/2`, usadas na expansão com `r` linhas
perturbadas. O próximo bloco aplica Taylor às linhas não perturbadas.
