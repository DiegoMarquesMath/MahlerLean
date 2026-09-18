# Etapa 8 — Zeros analíticos e localização por Wronskianos

Referência: o mesmo `paper/main.tex` da etapa 7. O artigo não foi alterado.
Lean e mathlib continuam nas revisões fixadas v4.24.0.

## O que foi provado

1. Se g é analítica numa vizinhança de um domínio preconexo U e existe
   y em U com g(y) diferente de zero, então g tem finitos zeros em qualquer
   compacto K contido em U. Infinitos zeros teriam um ponto de acumulação
   em K; o princípio de identidade daria g=0 em U, contradizendo y.
2. Para uma família finita dessas funções, a união de seus zeros em K
   é representada por um `Finset`, com equivalência exata de pertinência.
3. Numa parte compacta que evita os zeros, a continuidade fornece uma
   constante positiva que limita inferiormente todos os módulos. A
   constante pode depender da família finita e do compacto.
4. Dentro de qualquer intervalo compacto não degenerado contido em U,
   existe um intervalo compacto menor onde toda a família fica afastada
   de zero. Usamos a seleção quantitativa de intervalos já provada.
5. O Wronskiano é definido como o determinante das derivadas de ordens
   0,...,N-1. Sua analiticidade é provada por derivação, somas e produtos.
6. A família do artigo tem exatamente 2(d+1) funções, na ordem
   (0,0),(0,1),(1,0),(1,1),...,(d,1). Para o índice k usamos
   x^(k/2) f(x)^(k%2), com divisão inteira.
7. Para cada W_d não identicamente nulo, seus zeros num compacto são
   finitos. Qualquer coleção finita desses W_d admite localização
   simultânea com uma constante positiva.
8. Definimos D(A)=max(2,ceil(10A/97)) e provamos sua monotonicidade.
   Os conjuntos Z_n são exatamente as uniões dos zeros de W_d em I_*
   para 2<=d<=D(n+3); provamos Z_n contido em Z_m quando n<=m.

## Ligação com a fusão

A nova interface `WronskianCountingInputs f` tem como entradas:

- um domínio preconexo, a analiticidade de f e I_* contido no domínio;
- um limite superior M para |f'| e a constante Clow não negativa;
- para cada d>=2, a existência de um ponto onde W_d não se anula;
- a estimativa uniforme de contagem nos intervalos que evitam os zeros
  dos W_d do grau exigido.

Ela não pede uma sequência arbitrária de conjuntos finitos proibidos,
nem diferenciabilidade separada. Ambas são construídas a partir das
hipóteses analíticas. A oferta racional é a já provada na etapa 7.
`exists_escape_of_wronskian_counting` aplica a fusão a esses dados.

## O que continua pendente

**Esta etapa não prova que f não racional implica W_d não identicamente
nulo.** Faltam formalizar a equivalência entre racionalidade e dependência
linear e o critério analítico do Wronskiano. A hipótese de não anulação
idêntica está escrita explicitamente; não é um axioma novo.

Também faltam as estimativas uniformes de subníveis, suas decomposições
em intervalos, o argumento de determinantes e a Proposição 5.1. Os
Teoremas 1.1 e 1.2 ainda não estão integralmente formalizados.

## Arquivos e verificação

Novos módulos:

- `MahlerLean/AnalyticLocalization.lean`: 5 teoremas.
- `MahlerLean/WronskianLocalization.lean`: 6 teoremas.
- `MahlerLean/FusionFromWronskians.lean`: 4 teoremas.

Total: 96 teoremas auditados em 20 módulos. Veja `VALIDATION.md`.
A etapa 7 foi salva no GitHub no commit 58e6a52; a execução 35386107578
terminou com sucesso, conforme saída fornecida pelo usuário.

## Aplicar, verificar e salvar

Baixe `MahlerLean-step8.patch` para Downloads e execute o bloco abaixo.
Cada comando só prossegue se o anterior terminar com sucesso.

```bash
cd "/Users/diegomarques/Documents/Projetos/MahlerLean" &&
git apply --check "$HOME/Downloads/MahlerLean-step8.patch" &&
git apply "$HOME/Downloads/MahlerLean-step8.patch" &&
lake exe cache get Mathlib.Analysis.Analytic.IsolatedZeros Mathlib.Analysis.Calculus.FDeriv.Analytic Mathlib.Analysis.Calculus.IteratedDeriv.Defs Mathlib.LinearAlgebra.Matrix.Determinant.Basic &&
bash scripts/check.sh &&
git add MahlerLean.lean MahlerLean/AnalyticLocalization.lean MahlerLean/WronskianLocalization.lean MahlerLean/FusionFromWronskians.lean scripts/Audit.lean README.md VALIDATION.md docs/ROADMAP.md docs/STEP8_PT.md &&
git commit -m "Prove analytic zero localization and construct Wronskian fusion sets" &&
git push origin main &&
git status
```

Depois, consulte a verificação remota:

```bash
gh run list --repo DiegoMarquesMath/MahlerLean --limit 1
```

O envio usa sua sessão do terminal autenticada como DiegoMarquesMath.
A conexão GitHub desta conversa continua na conta DiegoNash e não tem
acesso ao repositório privado; este patch não foi enviado por ela.
