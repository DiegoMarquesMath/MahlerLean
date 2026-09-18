# Etapa 5 — Construção infinita e conclusão a partir da contagem

Registro da etapa 5. A etapa 6 acrescenta a separação de Farey e as cotas
superiores por intervalo e por componentes disjuntas. Veja
[STEP6_PT.md](STEP6_PT.md) para esses resultados; a oferta de racionais
e a Proposição 5.1 continuam pendentes.

Referência: o mesmo `paper/main.tex` das etapas anteriores, enviado em
18 de setembro de 2026, SHA-256
`4ac94b1f36e6a48103b25344e8e736657cef2cb5944c600c5afe098119f8b995`.
O manuscrito e as versões de Lean e mathlib não foram alterados.

## O que passa a estar formalizado

A etapa 4 produzia um intervalo filho a partir de hipóteses locais.
Agora construímos a sequência infinita, desde a escolha do intervalo
inicial e do primeiro corte, mantendo simultaneamente os invariantes
(F1)--(F7). A sequência fornece os dados exigidos pela conclusão da
etapa 3.

O teorema `exists_escape_of_counting` prova que, dadas as hipóteses
explícitas de `FusionInputs f`, existem um real x e um natural B tais que:

- x está no interior do intervalo ambiente;
- B >= 2;
- x é Liouville, tanto na definição da mathlib quanto na do artigo;
- para todo inteiro a e todo natural b >= B,
  `|f(x)-a/b| > b^(-100)`;
- f(x) não é Liouville.

Não se pressupõem centros seguros nem uma sequência de intervalos.
Sua existência é demonstrada a partir dos insumos de contagem.
**Esses insumos continuam sendo hipóteses: a Proposição 5.1, o Lema 2.2
e a parte analítica dos Wronskianos ainda não estão provados.**

## Hipóteses exatas de FusionInputs

| Campo | Conteúdo |
| --- | --- |
| `left`, `right`, `nondegenerate` | Intervalo ambiente fechado não degenerado |
| `M`, `M_nonneg` | Cota de derivada fixa, M >= 0 |
| `Clow`, `Clow_nonneg` | Constante Clow >= 0 fixa durante toda a recursão |
| `cF`, `cF_pos` | Constante de oferta cF > 0 fixa durante toda a recursão |
| `differentiable`, `deriv_bound` | Diferenciabilidade e `|f'| <= M` no ambiente |
| `zeros` | Uma sequência de conjuntos finitos Z_n de pontos proibidos |
| `supply` | `HasSourceSupply` em todo subintervalo compacto não degenerado do ambiente |
| `counting` | Para cada n e subintervalo J que evita Z_n, existe C com `HasUniformDangerBound` em J, para A = n+3 |

`HasUniformDangerBound` conserva a ordem dos quantificadores: existe
um limiar Q0 tal que a estimativa vale para todo H >= 2 e Q >= Q0.
Assim, C e Q0 podem depender de J e n, mas não de H. Clow é um único
campo da estrutura, independente de todos os intervalos e etapas.
O termo de resto continua sendo C Q^(17/10).

Na aplicação ao artigo, Z_n deverá conter os zeros dos Wronskianos
pertinentes a A_n = n+3. Demonstrar que esses conjuntos são finitos e
que sua exclusão permite aplicar a Proposição 5.1 é trabalho pendente.
A recursão em si não precisa supor que Z_n seja crescente: ela mantém
explicitamente a exclusão de Z_n na etapa n.

## Inicialização

`exists_initial_fusion_stage` obtém um intervalo fechado de comprimento
positivo no interior do ambiente, evitando Z_0, pelo lema geométrico da
etapa 4. Em seguida, `exists_initial_tail_cutoff` escolhe H >= 2 com

```text
Clow H^(-98) <= (cF/4) * (comprimento do intervalo / 3).
```

Isso é possível porque H^(-98) tende a zero. A inicialização fornece
as condições (F2) e (F7) sem assumi-las como dados externos.

## Recursão e invariantes

`FusionStage d n` guarda o intervalo atual, a exclusão de Z_n, o corte
atual e a condição de cauda. `exists_fusion_transition` aplica a oferta
e a contagem no terço médio e usa a etapa 4. O mínimo prescrito para Q
é `2*previousDen+1`, garantindo o crescimento dos denominadores.

`fusionStages` define a sequência por recursão sobre os naturais.
`fusionConstruction` reúne os dados e provas em `FusionConstruction d`,
uma extensão de `FusionData f` com os invariantes adicionais:

| Invariante do artigo | Campo formal |
| --- | --- |
| (F1), inclusão do filho no interior do pai | `nested_interior` |
| (F2), exclusão dos pontos proibidos da etapa | `avoids` |
| (F3), crescimento estrito dos cortes | `cutoff_strict` |
| (F4), q_(n+1) > 2 q_n | `denominator_growth` |
| (F5), aproximação fonte estrita e não nula | `source_approx` |
| (F6), exclusão dos alvos no bloco consecutivo | `target_avoid` |
| (F7), condição de cauda para o próximo centro | `tail` |

Os intervalos têm comprimento positivo e permanecem no interior do
ambiente. A função `fusionConstruction` usa escolha clássica e é marcada
`noncomputable`: isso impede extrair diretamente um algoritmo numérico
executável, mas não significa que existam provas faltantes. As provas
passam pelo kernel de Lean como as demais.

## Ponto comum e denominadores

`fusion_intersection_subsingleton` mostra que quaisquer dois pontos
comuns x,y satisfazem, para todo n,

```text
|x-y| <= 2 * 2^(-(n+3)).
```

A cota tende a zero. Junto com a existência obtida por compacidade,
isso dá `exists_unique_fusion_point`. A unicidade é da interseção da
sequência construída; não se afirma que exista apenas um ponto de
escape em todo o intervalo ambiente.

`fusion_denominators_tendsto` deduz q_n -> infinito do crescimento
estrito dos denominadores. A conclusão de Liouville também conserva
o erro estritamente positivo nas aproximações.

## Alcance e próximos passos

O projeto passa a conter 46 teoremas explicitamente declarados e
auditados, nove deles novos nesta etapa. Os novos módulos são
`FusionRecursion.lean` e `FusionEscape.lean`. O README lista todos os
novos teoremas, e `VALIDATION.md` registra a verificação realizada.

Está formalizada a implicação dos insumos de contagem para a construção
infinita e o ponto de escape. Faltam as provas que fornecem esses insumos
sob as hipóteses analíticas do manuscrito: oferta de racionais, análise
dos Wronskianos, Proposição 5.1 e suas dependências. Também permanece
pendente uma definição formal do expoente de irracionalidade e a ligação
com uma formulação explícita via mu.

Portanto, os Teoremas 1.1 e 1.2 ainda não podem ser apresentados como
integralmente formalizados. O resultado quantitativo já provado sob os
insumos é a desigualdade eventual com expoente 100.

## Aplicação e commit

Na pasta do projeto, verifique e aplique `MahlerLean-step5.patch` com
`git apply --check` e `git apply`. Execute `bash scripts/check.sh` antes
de fazer o próximo commit. Não é necessário atualizar dependências.

Mensagem sugerida para o commit local:

```text
Construct infinite fusion and derive escape from counting inputs
```

Esta atualização não publica o projeto no GitHub.
