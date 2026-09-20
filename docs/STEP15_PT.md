# Etapa 15 — localização da derivada

O módulo `AnalyticDerivativeInterval.lean` elimina os limites de derivada
como dados fornecidos à construção de fusão.

1. Uma função analítica não constante em um aberto conexo tem derivada
   não nula em algum ponto: caso contrário, o teorema do valor médio
   implicaria constância.
2. A derivada é analítica e não identicamente nula. O isolamento de zeros
   permite escolher, dentro de qualquer intervalo compacto não degenerado
   contido no domínio, um intervalo menor onde seu módulo tem limite
   inferior positivo.
3. A compacidade fornece o limite superior para o módulo da derivada.
4. A aplicação de `exists_escape_of_analytic_wronskians` fornece o ponto
   de escape sem pressupor limites de derivada ou estimativas de contagem.
5. O corolário `exists_escape_in_open_of_analytic_wronskians` funciona
   em qualquer aberto não vazio V contido no domínio U.

O resultado final produz x∈V, Liouville x, e B≥2 tal que
abs(f(x)-p/q)>q^(-100) para todos p inteiros e q≥B naturais, além de
não ser Liouville f(x).

## Hipóteses restantes

Analiticidade, domínio aberto preconexo, não constância, e:
para cada d≥2 existe y∈U com W_d(y)≠0.

A implicação **não racionalidade ⇒ não trivialidade dos Wronskianos**
ainda não foi formalizada. Ela requer conectar independência linear da
família x^i f(x)^j ao critério analítico do Wronskiano. A busca no diretório
Analysis da versão fixada da mathlib não encontrou um teorema pronto
com o nome Wronskian. Não se tomou essa implicação como axioma.

## Validação

Os quatro teoremas do módulo foram compilados com warnings como erros.
A auditoria transitiva lista somente propext, Classical.choice e Quot.sound.
O Teorema 1.2 a partir da não racionalidade ainda não é anunciado como concluído.
