# Etapa 16 — relações polinomiais e não racionalidade

`IsRationalOn f U` significa que existem P,Q em ℝ[X], Q não nulo,
Q(x)≠0 em todo U e f(x)=P(x)/Q(x) em U. Assim a negação é exatamente
a ausência de uma representação racional sem polos no domínio.

## Resultado algébrico-analítico

`isRationalOn_of_polynomial_relation` prova que uma relação A+Bf=0,
com B não nulo, implica essa racionalidade quando f é analítica em um
aberto preconexo não vazio.

A prova extrai D=gcd(A,B), A=DP, B=DQ, com P,Q coprimos.
A identidade D(x)(P(x)+Q(x)f(x))=0 e a analiticidade implicam que
D se anula identicamente ou P+Qf se anula identicamente. O primeiro
caso é impossível: um polinômio não nulo não se anula em um aberto real.
No segundo, a coprimalidade impede qualquer zero de Q no domínio,
pois esse seria também um zero de P. Logo f=-P/Q em todo U.

`polynomial_relation_eq_zero_of_not_rational` deduz que, sob não
racionalidade, A+Bf=0 implica A=B=0. Essa é a parte polinomial da
independência da família usada pelo artigo. A conversão completa para
a declaração de independência linear da família indexada e o critério
analítico do Wronskiano não são anunciados como concluídos.

## Ligação à conclusão

`nonconstant_of_not_rational` elimina a hipótese separada de não
constância. O novo teorema
`exists_escape_of_not_rational_and_wronskians` recebe a não
racionalidade original e produz o escape em cada aberto V não vazio.
A não trivialidade dos Wronskianos permanece explicitamente como hipótese.

## Validação

Módulo compilado com Lean 4.24.0 e warnings como erros.
Os cinco teoremas foram auditados transitivamente: apenas
propext, Classical.choice e Quot.sound, sem sorryAx.
Validação direcionada; não é uma afirmação de novo CI completo aprovado.
