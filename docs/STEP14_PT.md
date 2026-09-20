# Etapa 14 — correspondência da contagem e ligação à fusão

## Conferência com o manuscrito

Referência: `paper/main.tex` no commit `1cd6a0b2a8692b5278365c34ef60571a5fa48081`,
Proposição `prop:scarcity-en` e as definições imediatamente anteriores.
Esta é uma comparação matemática dos enunciados e definições; o kernel
verifica o enunciado Lean, não o texto LaTeX.

| Manuscrito | Lean | Correspondência |
| --- | --- | --- |
| Intervalo ambiente compacto I_* | `Icc a b` | Analiticidade em aberto contendo o intervalo. |
| m_*>0 e m_*≤abs(f')≤M_* | `hm`, `hdm`, M | A contagem requer apenas M≥0; a cota superior volta a ser usada na fusão. As hipóteses do artigo implicam M≥0. |
| J compacto não degenerado | `Icc l u`, `l<u` | Inclusão no intervalo ambiente explícita. |
| Fonte reduzida, Q≤q<2Q | `sourceFractions`, `Rat.den` | `mem_sourceFractions` caracteriza exatamente esse conjunto. |
| Witness a inteiro, b positivo, H≤b<T | `HasTargetWitness` | Não há exigência adicional de coprimalidade no alvo. |
| T=Q^(A/97) | `targetCutoff` | Mesma potência real. |
| Margem 2 b^(-100)+4 M_* Q^(-A) | `safetyMargin` | Inversas de potências naturais, equivalentes para denominadores positivos. |
| D(A)=max(2,ceil(10A/97)) | `wronskianDegreeCutoff` | Teto natural coincide para A≥3. |
| Família x^i f(x)^j, j=0,1 | `rationalFamily` | Ordem lexicográfica; `rationalWronskian` é o determinante das derivadas. |
| C_low antes de J,A | `proposition_5_1` | Mesma ordem de quantificadores. |
| C(J,A), Q₀(J,A) antes de H | `proposition_5_1` | Uniformidade em H preservada. Q₀ natural positivo; pode ser aumentado para max(2,Q₀). |
| C_low Q² H^(-98)+C Q^(17/10) | Conclusão Lean | Mesmos expoentes e conjunto contado. |

Conclusão da comparação: a estimativa formalizada implica a Proposição 5.1
do manuscrito referenciado, com suas hipóteses herdadas da seção.
A não racionalidade e a conexidade do domínio não precisam ser acrescentadas
à prova da contagem quando a não anulação dos Wronskianos em J já é assumida.
O limite da imagem é obtido por compacidade, não imposto como hipótese extra.

A função Lean é total em ℝ; apenas seus valores e germes no aberto U são usados.
Uma função do artigo definida somente em U pode ser estendida fora desse
aberto sem alterar os germes relevantes. Não se afirma que o Lean leia ou
verifique automaticamente a representação LaTeX do artigo.

## Ligação provada à fusão

`FusionFromTwoHeight.lean` prova
`exists_escape_of_analytic_wronskians`.
A prova instancia `WronskianCountingInputs`, preenchendo seu campo
`counting` com `proposition_5_1_uniformDangerBound`.
Assim, nenhuma estimativa de contagem permanece como hipótese do novo teorema.

Sob analiticidade em U aberto e conexo, limites positivo inferior e superior
para abs(f') em [a,b], e não trivialidade de cada W_d em U, o teorema produz:

- x em (a,b), com `Liouville x` e `PaperLiouville x`;
- um B≥2 tal que, para todo inteiro p e natural q≥B,
  `q^(-100) < abs(f(x)-p/q)`;
- `¬ Liouville (f x)`.

A cota explícita de aproximação é preservada, não apenas a conclusão de
não ser Liouville. Não foi introduzida nesta etapa uma definição formal
do expoente de irracionalidade μ.

## Validação e limite do resultado

O módulo compilou em Lean 4.24.0 com warnings como erros.
A auditoria transitiva do novo teorema lista somente
`propext, Classical.choice, Quot.sound`, sem `sorryAx`.
Esta validação é do módulo e do teorema; não é uma alegação de nova execução
completa do CI.

Ainda falta, para o Teorema 1.2 a partir das hipóteses originais:
deduzir a não trivialidade de todos os Wronskianos a partir da não
racionalidade; obter um intervalo com os limites de derivada dentro de
cada subintervalo aberto pretendido; aplicar o novo teorema a esses dados.
Essas implicações não estão escondidas em hipóteses de contagem.
