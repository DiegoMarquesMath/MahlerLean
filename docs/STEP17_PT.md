# Etapa 17 — independência da família e dos germes

O módulo `RationalFamilyIndependent.lean` conclui a passagem da
não racionalidade à independência da família exata usada no Wronskiano.

`relationPolynomial` separa os coeficientes de índices pares e ímpares.
`relationPolynomial_coeff` recupera cada coeficiente, sem identificações
informais de índices. `relationPolynomial_eval` identifica a combinação
da família com A(x)+B(x)f(x).

`rationalFamily_linearIndependent_of_not_rational` prova independência
linear sobre ℝ das funções restritas a U, indexadas por Fin(2(d+1)),
para todo d natural. A ordem é a mesma de `rationalFamily` e
`rationalWronskian`.

`rationalFamily_coeff_eq_zero_of_eventually_sum_eq_zero` prova a versão
local: em qualquer z∈U, se a combinação se anula numa vizinhança de z,
todos os coeficientes são zero. A prova usa o teorema de identidade
analítica no domínio preconexo.

## Estado do critério do Wronskiano

A independência linear global e local está provada.
Ainda não está provado que essa independência implique W_d não
identicamente nulo. Não se deve substituir essa implicação pela afirmação
falsa de que W_d é não nulo em todo ponto.

Uma rota para a próxima formalização é escolher uma base de germes com
ordens de anulação distintas e calcular o primeiro coeficiente do
Wronskiano pelas séries de Taylor. O fator determinante das potências
decrescentes é de Vandermonde e é não nulo para ordens distintas.
Essa rota é uma proposta de implementação, não um resultado Lean já concluído.

## Validação

Os quatro teoremas compilaram com warnings como erros. A auditoria transitiva
lista somente propext, Classical.choice, Quot.sound, sem sorryAx.
O Teorema 1.2 continua pendente do critério analítico do Wronskiano e da
aplicação final. Não se afirma nesta nota uma nova execução completa do CI.
