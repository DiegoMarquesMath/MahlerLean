# Etapa 13: do determinante à contagem uniforme

Esta etapa formaliza o núcleo do método do determinante usado na
Proposição 5.1. Ela ainda não declara a proposição completa: faltam a montagem
simultânea das células e escalas e a soma final dos blocos de alturas-alvo.

## Resultados verificados

1. `targetLinearMatrix_det_lower_dyadic` mantém separadas as alturas da fonte
   e do alvo ao limpar denominadores.
2. `exists_targetLinearMatrix_analytic_upper_bound` controla o determinante
   por
   `K * (rho^(N*(N-1)/2) + delta)`.
3. `exists_targetLinearMatrix_det_zero_of_clustered_approximations` compara
   os limites analítico e aritmético e força o determinante a ser zero.
4. `exists_unit_relation_of_all_det_zero` prova o passo abstrato de posto:
   se todos os menores máximos se anulam, existe uma relação comum com
   vetor de coeficientes de norma um.
5. `exists_unit_targetLinear_graph_sublevel_of_all_det_zero` transfere a
   relação exata nos valores racionais aproximantes para uma relação pequena
   no gráfico analítico.
6. `exists_uniform_analytic_sublevel_disjoint_interval_cover` produz uma
   união exata de intervalos dois a dois disjuntos, com número uniformemente
   limitado.
7. `exists_targetLinear_counting_bound_of_all_det_zero` combina a relação, o
   limite uniforme de subnível e a separação de Farey numa estimativa de
   contagem para qualquer conjunto racional finito que satisfaça as hipóteses
   de anulação.

Todos esses resultados são compilados com `-DwarningAsError=true` e entram na
auditoria de axiomas. As únicas dependências lógicas impressas são as usuais
da biblioteca (`propext`, `Classical.choice` e `Quot.sound`).

## Próximo bloco

O próximo passo deve construir, a partir dos testemunhos racionais da
Proposição 5.1, a família finita à qual o teorema de contagem acima se aplica:

- escolher uma aproximação-alvo por centro;
- verificar a anulação para toda seleção de `N = 2(d+1)` centros na mesma
  célula;
- inserir as escolhas de `d`, `rho`, `delta`, `Q` e `H` já controladas pelos
  lemas de parâmetros grandes;
- somar os blocos de alturas-alvo preservando a perda de expoente prevista no
  artigo.

Somente depois dessa montagem o projeto poderá afirmar a Proposição 5.1 na
forma usada pela construção de fusão.

## Montagem das somas e pendência do determinante

`CellCountingAssembly.lean` formaliza a soma das contagens sobre uma
cobertura finita (sem hipótese de disjunção), a multiplicação de uma cota
uniforme por célula pelo número de células e a absorção eventual
`log Q * Q^(33/20) ≤ Q^(17/10)`.
Esses lemas ainda não constroem as células nem contam os blocos diádicos.

O enunciado em `paper/main.tex` pede o expoente `17/10`, com constantes
independentes de H. A montagem deve seguir esse enunciado.

Há uma pendência anterior à montagem final: a cota atualmente formalizada
em `TargetLinearDeterminantUpper.lean` tem a forma
`K * (rho^(N*(N-1)/2) + delta)`. O artigo utiliza a estimativa perturbada
mais forte, preservando a potência do comprimento da célula quando
`delta ≤ rho^N`. A cota aditiva existente não fornece automaticamente
esse resultado. Por exemplo, para u=10, d=100, N=202 e A=1000, a
escala aritmética tem expoente N(d+u)=22220, enquanto s=min(100u,A)=1000.
Assim, o termo aditivo de erro não é pequeno o suficiente para a comparação
assintótica nessa escolha. Isso identifica uma lacuna na formalização,
não uma refutação do lema perturbado do artigo.

A continuação abaixo prova a versão forte com base fixa. A uniformidade
na posição das células permanece necessária.

## Expansão multilinear e limiar uniforme

A origem exata da perda foi identificada em
`abs_det_add_le_of_remainder_rows`: após selecionar uma linha pequena,
as demais são estimadas individualmente por B, perdendo o decaimento
conjunto dos vetores da curva.

A nova rota preserva essa informação sem exigir Wronskianos não nulos:

- `SmoothCurveMinorDecay.lean` prova o decaimento triangular para os menores
de m linhas da curva, uniformemente nas escolhas de coordenadas, incluindo
m=0 e m=1.
- `MixedDeterminantDecay.lean` usa expansão de Laplace pelas linhas de erro
para obter os fatores delta^r e rho^((N-r)(N-r-1)/2). A prova combina esses
fatores na expansão multilinear já existente. Os fatores combinatórios
são absorvidos numa constante finita.
- `exists_smooth_curve_perturbed_sum_bound` estabelece a versão matricial
de (4.8) para pontos próximos de uma base de Taylor fixa.
- `exists_targetLinearMatrix_strong_perturbed_bound` dá o corolário forte
para a curva alvo-linear sob delta ≤ rho^N, sem hipótese sobre Wronskianos.
- `MultilinearPerturbation.lean` prova (4.9), a absorção dos termos da soma
e `largeTarget_vertical_error_le_radius_power`, que liga diretamente
s-kappa*N ≥ 1/5 ao limiar Q ≥ K0^5. Esse limiar não depende de u, B ou H.

Os novos arquivos foram compilados com warningAsError=true e os resultados
principais auditados: somente propext, Classical.choice e Quot.sound.

Limite preciso: as constantes analíticas acima ainda são escolhidas para
um intervalo e sua extremidade esquerda fixos. Para concluir o lema do
artigo em toda célula móvel dentro de J, falta extrair os limites de
Taylor/derivadas uniformemente na base em J. Só depois essa estimativa
substituirá a interface usada na montagem global da Proposição 5.1.
A alternativa por inversão da matriz de derivadas não foi incorporada.

## Uniformidade na posição da célula — concluída

A restrição à base fixa do bloco anterior foi removida:

- `UniformTaylorBase.lean` escolhe limites das derivadas e do resto de
Taylor no intervalo compacto pai [a,b], antes de escolher a base c.
A igualdade das derivadas nas restrições [c,b] é provada explicitamente.
- `UniformCurveDeterminant.lean` propaga esses limites ao decaimento de
cada menor, incluindo os tamanhos 0 e 1.
- `UniformPerturbedDeterminant.lean` prova a soma de termos mistos e a
estimativa forte, com a constante independente de c, rho, delta e dos
pontos escolhidos. As células satisfazem a ≤ c < b e c ≤ x_i ≤ b,
x_i-c ≤ rho.
- `UniformDeterminantVanishing.lean` escolhe uma constante única antes
do grau d≤D e da célula, e compara a estimativa forte com a cota
aritmética dos denominadores para forçar o determinante a zero.

A versão forte não usa Wronskianos nem matriz inversa. Ela depende somente
da regularidade da curva no intervalo pai e da hipótese delta ≤ rho^N.
A uniformidade analítica necessária para as células está, portanto,
formalizada. Os onze resultados principais passaram por compilação com
warningAsError=true e auditoria com os três axiomas padrão.

Próximo trabalho: verificar uniformemente a desigualdade estrita entre
K*rho^(N(N-1)/2) e o limiar aritmético após inserir as escalas do artigo;
construir as famílias de centros com testemunhos, aplicar a contagem,
e concluir as somas de células e blocos. A Proposição 5.1 completa ainda
não é declarada como concluída.

## Escalas, witnesses e contagem por célula — avanço seguinte

A comparação estrita dos determinantes foi fechada com as escalas do artigo.
`DeterminantScaleComparison.lean` verifica o ganho de pelo menos uma potência
de Q e a identidade exata do fator dos denominadores. Para d ≤ D, o fator
2^(dN+N) é dominado por 2^(D·2(D+1)+2(D+1)).

`exists_largeTarget_det_zero_uniform_threshold` escolhe um único Q₀ antes de
u e da célula. Com d=ceil(10u), N=2(d+1), κ e s do artigo, u≥1/5 e 97u<A,
ele deduz o anulamento do determinante diretamente dos limites de denominadores,
da geometria da célula e da aproximação vertical K₀ Q^(-s).
O limiar absorve simultaneamente K₀^5 e a constante do determinante.
Não restam hipóteses de comparação estrita nem de δ≤ρ^N nesse enunciado.

`LargeTargetWitnesses.lean` escolhe um witness racional por ponto fonte de uma
família finita e estabelece o anulamento para todas as tuplas, com repetições.
O corolário `exists_largeTarget_cell_counting_data` conecta essa construção à
contagem de Farey/subnível, assumindo os Wronskianos apenas para 2≤d≤D(A).

**Limite exato deste avanço:** o corolário de contagem ainda explicita o limiar
de subnível eps0. Seus dados C, R, eps0 são escolhidos após u; é necessário
uniformizá-los sobre os graus finitos, absorver o limiar e somar células e blocos.
O regime de pequenas alturas e a montagem integral da Proposition 5.1
continuam pendentes. Não se declara concluído o Theorem 1.2.

Validação: os três novos módulos compilaram com warningAsError=true.
Os oito resultados novos foram auditados: somente propext, Classical.choice
e Quot.sound. Esta validação é direcionada aos módulos novos; o CI completo
é uma verificação separada.

## Item 1: dados uniformes de subnível e cota por célula — concluído

Este avanço resolve a pendência de uniformidade indicada na seção anterior.

- `UniformDegreeCounting.lean` escolhe C>0, R>0 e eps>0 antes do grau:
  os mesmos dados valem para todo 2≤d≤D. As hipóteses de Wronskianos
  são exigidas apenas nesse intervalo de graus.
- `UniformSublevelThreshold.lean` domina N X^d K₀ por
  L = 2(D+1) X^D K₀. Como s≥97u≥97/5>1, o limiar
  Q≥max(1,L/eps+1) garante N X^d K₀ Q^(-s)<eps
  uniformemente. Ele é combinado com o limiar já provado dos determinantes.
- `UniformLargeTargetCounting.lean` escolhe as constantes e Q₀ antes de u,
  Q, da célula e da família finita de pontos fonte. A condição de pequenas
  perturbações foi eliminada das hipóteses.

O resultado final
`exists_uniform_largeTarget_interval_cell_card_bound` fornece M>0 e Q₀≥1,
dependentes apenas dos dados fixos f, U, [a,b], A e K₀. Para Q≥Q₀, u≥1/5,
97u<A e qualquer célula admissível de comprimento Q^(-κ), toda família
finita de fontes racionais com denominadores <2Q e witnesses de denominador
≤2Q^u, erro ≤K₀Q^(-s), tem cardinalidade ≤M.

A cota constante usa s/(N−1)>2: o decaimento de subnível absorve o fator Q²
da contagem de Farey. O limite |x|≤X não é uma hipótese adicional no
resultado final: X=max(1,|a|,|b|) é escolhido a partir do intervalo fixo.
Nenhuma constante depende do bloco alvo, da célula ou de um cutoff H.

**Próximas pendências:** construir/somar as células que cobrem o conjunto de
fontes de cada bloco grande, somar os blocos e combinar o regime de pequenas
alturas no enunciado integral da Proposition 5.1. O Theorem 1.2 permanece
pendente.

Validação: os três novos módulos compilaram com warningAsError=true.
Os oito resultados novos foram auditados e dependem apenas de propext,
Classical.choice e Quot.sound. O build/CI integral é uma verificação separada.

## Item 2: soma das células e dos blocos grandes — concluído

A contribuição completa dos blocos grandes tem agora cota C Q^(17/10),
com C e Q₀ escolhidos antes de H≥1.

1. `SourceCellCover.lean` constrói uma cobertura de [a,b] por
   ceil((b-a)/rho) células, incluindo o extremo direito. Cada base c satisfaz
   a≤c<b. O número de células é ≤(b-a)/rho+1.
2. `LargeTargetBlockCounting.lean` aplica a cota uniforme por célula e
   κ≤33/20 para obter uma cota C Q^(33/20) por bloco. A cobertura e a
   contagem das células são provadas, não hipóteses do resultado.
3. `DyadicTargetBlocks.lean` mostra que 2^k H<Q^(A/97), H≥1 implica
   k<ceil((A/97)log Q/log 2), e limita essa quantidade por
   ((A/97+1)/log 2)log Q. Também verifica u=log_Q(2^k H), u≥1/5 e 97u<A
   para os blocos grandes.
4. `LargeTargetDyadicCounting.lean` constrói os subconjuntos finitos
   associados aos blocos e soma as suas cotas. Possíveis sobreposições
   apenas produzem uma sobrecontagem. O lema de absorção logarítmica já
   existente dá Q^(33/20)log Q≤Q^(17/10) para Q suficientemente grande.
5. `LargeTargetSafetyMargin.lean` liga a soma ao erro original
   safetyMargin = 2 b^(-100)+4M Q^(-A), usando K₀=2+4M. Os witnesses
   inteiros p,b não precisam estar em forma reduzida: a redução só diminui
   o denominador usado no determinante, enquanto a estimativa de erro usa
   o denominador original b.

O teorema final `exists_largeTarget_original_margin_card_bound` vale para
qualquer família finita de fontes em [a,b], com denominadores <2Q, cada uma
admitindo witness em algum bloco B=2^k H com Q^(1/5)≤B<Q^(A/97) e
B≤b<2B, com o erro original. Ele conclui #S≤C Q^(17/10).
Não há hipóteses de número de células, número de blocos ou constante
dependente de H.

**Restam:** a contagem dos blocos pequenos e a decomposição/montagem do
conjunto dangerousSources no enunciado integral da Proposition 5.1.
Blocos que começam abaixo de Q^(1/5), mesmo cruzando esse limiar, continuam
atribuídos ao regime pequeno, conforme o artigo. Theorem 1.2 não está concluído.

Validação: os cinco novos módulos compilaram com warningAsError=true.
Os nove resultados foram auditados: apenas propext, Classical.choice e
Quot.sound. Não se confunde essa validação direcionada com o CI integral.
