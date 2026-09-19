# Etapa 11 — estimativa unidimensional de subnível

Esta etapa formaliza o Lemma 3.4 usado posteriormente no Lemma 3.5.

O módulo principal é:

`MahlerLean/SublevelOneDim.lean`

Suponha que `g : R -> R` seja suficientemente diferenciável em `[a,b]`
e que, para algum inteiro positivo `k`,

`lambda <= |g^(k)(x)|`

uniformemente no intervalo, com `lambda > 0`.

A etapa prova o controle quantitativo do conjunto de subnível

`E_eps = {x in [a,b] : |g(x)| <= eps}`.

## Rolle iterado e level sets

A formalização começa com versões iteradas do teorema de Rolle. Em
particular, `k+1` zeros ordenados de uma função forçam um zero da
`k`-ésima derivada.

Isso fornece controle dos conjuntos de nível:

- `level_hit_finset_card_le`
- `level_hit_set_finite`
- `two_level_set_finite_and_ncard_le`
- `abs_boundary_set_finite_and_ncard_le`

Como consequência, o conjunto de fronteira

`{x in [a,b] : |g(x)| = eps}`

tem no máximo `2k` pontos.

## Diferenças finitas

A etapa também formaliza o vínculo entre diferenças finitas iteradas e
derivadas iteradas:

- `norm_fwdDiff_iter_le_two_pow_mul`
- `hasDerivAt_fwdDiff_iter`
- `exists_fwdDiff_iter_eq_pow_mul_iteratedDeriv`

A partir disso obtém-se o bound de comprimento para qualquer intervalo
inteiramente contido no subnível:

`sublevel_interval_length_bound`

que prova

`v-u <= 2k (eps/lambda)^(1/k)`.

## Decomposição pela fronteira

Como há no máximo `2k` pontos de fronteira, o intervalo é cortado em no
máximo `2k+1` regiões relevantes.

Os teoremas

- `sublevel_gap_measure_bound`
- `sublevel_measure_le_of_boundary_finset_aux`

formalizam essa decomposição e a soma das contribuições.

## Estimativa final

O teorema principal da etapa é

`sublevel_measure_bound`.

Ele prova explicitamente

`volume(E_eps) <= 2k(2k+1)(eps/lambda)^(1/k)`.

Essa é a estimativa quantitativa unidimensional necessária para o passo
seguinte da formalização.

## Verificação

Todos os teoremas da etapa foram adicionados a `scripts/Audit.lean`.
O projeto possui agora 151 teoremas listados no audit.

Os novos resultados dependem apenas dos axiomas fundacionais usuais
`propext`, `Classical.choice` e `Quot.sound`; não aparece `sorryAx`
nem axioma específico do projeto.

O próximo passo é combinar esta estimativa com os lower bounds uniformes
de jatos da Etapa 10 para formalizar o Lemma 3.5 e o Corollary 3.6.
