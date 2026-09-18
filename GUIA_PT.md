# MahlerLean: do primeiro download ao GitHub

Este guia usa macOS como referência. O objetivo inicial é instalar o ambiente,
abrir este projeto, verificar pequenos lemas e guardar o histórico no GitHub.
A formalização completa do artigo é o trabalho matemático que virá depois.

## 1. O que é cada programa

| Nome | Função |
| --- | --- |
| Lean 4 | Linguagem e verificador das demonstrações |
| VS Code | Editor onde você escreve e vê os objetivos da prova |
| Extensão Lean 4 | Integra Lean ao editor e orienta a instalação |
| Elan | Seleciona a versão de Lean exigida pelo projeto |
| Lake | Gerencia dependências e compila o projeto |
| mathlib | Biblioteca de matemática formalizada |
| Git | Histórico local das alterações |
| GitHub | Hospeda o repositório e executa verificações remotas |

Você não precisa pagar pelo Lean, VS Code ou mathlib.

## 2. Instalar no Mac

1. Acesse https://lean-lang.org/install/ e siga o link oficial para VS Code.
2. Baixe a edição apropriada para seu Mac. Abra o arquivo baixado e mova
   Visual Studio Code para Applications/Aplicativos.
3. Abra VS Code. Na barra lateral, abra Extensions/Extensões, ou use
   Cmd+Shift+X. Procure `Lean 4` e instale a extensão do publicador
   `leanprover` (identificador `leanprover.lean4`).
4. Abra o guia de configuração da extensão e siga os passos. Se ele não
   aparecer, crie um arquivo vazio com Cmd+N, clique no símbolo ∀ no canto
   superior direito e selecione Documentation > Docs: Show Setup Guide… .
5. Conclua a instalação das ferramentas que o guia solicitar. Ele orienta
   a configuração de Elan e Lean; não é preciso baixar uma segunda cópia
   manual de Lean.
6. Se Git estiver ausente, o guia pode indicar a instalação. No terminal
   do macOS, `git --version` normalmente oferece instalar as ferramentas
   de linha de comando da Apple quando necessário. Não é necessário instalar
   o aplicativo Xcode completo apenas para isso.
7. Feche e abra novamente o VS Code depois da instalação, para que ele
   reconheça os comandos novos.

Se o instalador informar incompatibilidade, registre a versão do macOS em
menu Apple > Sobre Este Mac e a mensagem exata antes de tentar outra rota.

## 3. Abrir este projeto

1. Descompacte `MahlerLean-starter.zip`.
2. Mova a pasta `MahlerLean` para uma localização definitiva, por exemplo
   `Documentos/Projetos/MahlerLean`.
3. No VS Code, use File > Open Folder… e escolha a pasta `MahlerLean` inteira.
   A pasta correta contém `lean-toolchain` e `lakefile.toml`.
4. Abra Terminal > New Terminal. Confira que o terminal está nessa pasta.
5. Rode os comandos abaixo, um por vez. Espere cada um terminar.

```bash
lake update
lake exe cache get
lake build
bash scripts/check.sh
```

`lake update` resolve as dependências configuradas e cria/atualiza
`lake-manifest.json`. `lake exe cache get` baixa os arquivos já compilados
de mathlib. `lake build` verifica os módulos importados pelo projeto.
O último comando verifica os arquivos e imprime os axiomas dos nove lemas.
O primeiro download pode ser considerável e depende da sua conexão.

O projeto fixa Lean e mathlib em `v4.24.0`, uma base reproduzível.
Elan baixa/seleciona essa versão automaticamente. Não altere apenas a versão
de Lean: Lean e mathlib precisam continuar compatíveis.

Abra `MahlerLean/Parameters.lean`. Espere o processamento terminar. Coloque
o cursor dentro de uma prova e observe o Lean Infoview. No fim de uma prova
completa aparece normalmente `No goals`. A verificação do projeto inteiro
continua sendo feita pelos comandos acima.

## 4. Entender o primeiro exemplo

```lean
import Mathlib.Tactic.NormNum

example : (33 : ℚ) / 20 + 1 / 20 = 17 / 10 := by
  norm_num
```

`import` carrega os resultados necessários. `(33 : ℚ)` diz que 33 está nos
racionais. Depois de `by` vem a prova. `norm_num` produz uma prova da conta,
que Lean verifica. Isto certifica a identidade numérica; não certifica a
estimativa analítica onde ela será usada.

Para escrever ℚ digite `\Q` e espaço; para ℝ digite `\R` e espaço.
Você também pode copiar os símbolos diretamente.

O arquivo `SafeCenter.lean` contém um passo mais próximo do artigo:
transferir a margem de segurança de f(r) para f(x), por desigualdade triangular.
Os enunciados do teorema principal e da Proposição 5.1 ainda não estão provados.

## 5. Guardar no GitHub pelo caminho visual

Crie uma conta em https://github.com/ se ainda não tiver uma. Instale GitHub
Desktop por https://desktop.github.com/ e faça login pelo próprio aplicativo.

Na pasta do projeto, pelo terminal integrado do VS Code, execute:

```bash
git init -b main
```

Esse comando cria o histórico local; ainda não envia nada. No GitHub Desktop:

1. Use File > Add Local Repository… e escolha a pasta `MahlerLean`.
2. Confira a lista de arquivos. Os fontes, o guia, a configuração e
   `lake-manifest.json` devem entrar. A pasta de dependências `.lake` está
   excluída pelo `.gitignore`.
3. No campo Summary, escreva `Initial Lean project and supporting lemmas`.
4. Clique Commit to main.
5. Clique Publish repository; escolha o nome `MahlerLean`.
6. Recomendo começar com Keep this code private marcado. A publicação
   pública pode ser feita quando o escopo estiver revisado.
7. Clique Publish Repository.

O pacote não inclui o PDF do manuscrito. O repositório inicial contém apenas
o código e a documentação do projeto. A licença de reutilização ainda não
foi escolhida; decida isso quando for abrir o projeto para colaboradores.

Se você já usa GitHub pela extensão do VS Code ou pelo terminal, pode usar
esse fluxo em vez do GitHub Desktop. Não é necessário usar dois métodos.

## 6. Verificação automática

O pacote contém `.github/workflows/lean.yml`. Depois do primeiro envio, abra
a aba Actions no repositório. O fluxo `Lean verification` instala o ambiente,
compila o projeto e executa a auditoria dos lemas listados.

Um resultado verde se refere ao código presente nessa revisão. Ele não
significa que o artigo inteiro foi formalizado. Se aparecer vermelho, abra
a execução e a primeira etapa que falhou; copie a mensagem completa.

`sorry` permite deixar uma lacuna durante a escrita; sua presença pode
produzir apenas um aviso numa compilação comum. Por isso usamos avisos como
erros e inspecionamos os axiomas das declarações principais. `sorryAx` indica
dependência de uma lacuna. Os axiomas usuais `propext`, `Classical.choice` e
`Quot.sound` são compatíveis com a matemática clássica utilizada aqui.
Também precisamos conferir se o enunciado formal corresponde ao do artigo.

## 7. Rotina de trabalho

1. Escrevemos um enunciado pequeno e conferimos suas hipóteses.
2. Construímos a prova observando os objetivos do Infoview.
3. Adicionamos o módulo aos imports de `MahlerLean.lean` e o resultado à
   lista de `scripts/Audit.lean`.
4. Executamos `lake build` e `bash scripts/check.sh`.
5. Fazemos um commit com uma descrição concreta e usamos Push origin no
   GitHub Desktop para enviar as alterações.
6. Conferimos a execução da aba Actions.

Não use `lake update` a cada sessão. Mantenha as versões estáveis durante
uma etapa da formalização. Trabalhe em uma branch separada para atualizá-las.

## 8. Primeiros marcos matemáticos

O roteiro completo está em `docs/ROADMAP.md`. O primeiro marco substancial
será formalizar a construção de intervalos da Seção 6, com os resultados
anteriores ainda não formalizados apresentados como hipóteses explícitas.
Depois preencheremos essas dependências, em especial a Proposição 5.1.

Um site de blueprint como o do projeto PFR pode ser acrescentado depois.
Não é necessário configurar site, domínio, Python ou LaTeX para começar a
verificar estas primeiras provas em Lean.

## 9. Problemas frequentes

| Mensagem/situação | Primeira providência |
| --- | --- |
| `lake: command not found` | Reabra VS Code e conclua o guia da extensão |
| Lean reclama de projeto ausente | Abra a pasta que contém `lakefile.toml` |
| `unknown module prefix Mathlib` | Confira a pasta e execute os dois primeiros comandos de instalação |
| Incompatibilidade de versão | Restaure o par Lean/mathlib fixado no projeto |
| Infoview não aparece | Experimente Cmd+Shift+Enter ou os comandos da extensão |
| Actions falhou | Abra a primeira etapa vermelha e copie o erro completo |

Para pedir ajuda, envie uma captura do erro e o resultado de `lake env lean
--version`, executado na pasta do projeto. Não envie senhas ou tokens.

## Fontes oficiais

- Instalação: https://lean-lang.org/install/
- Extensão: https://marketplace.visualstudio.com/items?itemName=leanprover.lean4
- Projetos com mathlib: https://leanprover-community.github.io/install/project.html
- CI: https://github.com/leanprover/lean-action
- GitHub Desktop: https://docs.github.com/en/desktop/adding-and-cloning-repositories/adding-an-existing-project-to-github-using-github-desktop
- Aprendizado: https://leanprover-community.github.io/mathematics_in_lean/

Guia preparado em 18 de setembro de 2026. Consulte `VALIDATION.md` para
saber exatamente quais verificações foram executadas antes da entrega.
