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

## Próximos blocos

1. Decaimento de determinantes ao longo de uma curva suave, com expoente N(N−1)/2.
2. Controle da perturbação vertical, conservando esse expoente.
3. Aplicação a todos os menores máximos e extração de uma relação com
   coeficientes normalizados.
4. Integração com os subníveis e a contagem da Proposição 5.1.

Este bloco conclui o lema aritmético de limpeza de denominadores.
Não conclui toda a etapa de determinantes nem a Proposição 5.1.

## Verificação

As seis declarações estão incluídas em `scripts/Audit.lean`.
O workflow da branch compila o projeto e executa `bash scripts/check.sh`,
com avisos tratados como erros e inspeção das dependências axiomáticas.
