# html5lib tree-construction tests (`.dat`), as maintained in WPT

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/html/syntax/parsing/resources
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
Date: 2026-10-19 (commit date of the WPT commit above)
License: BSD-3-Clause (WPT) for the files as vendored; they originated in html5lib-tests under MIT. `LICENSE.md` holds both texts: WPT's `LICENSE.md` from the repository root at the commit above, byte for byte, then html5lib-tests' `LICENSE`.

## Where the files come from

html5lib-tests (https://github.com/html5lib/html5lib-tests) no longer has
`tree-construction/`: at its current commit
c777c408b61078ea2eb4acefc2535f54dbc8b28a (2026-09-29) its README says the
tree construction tests are "now solely maintained on web-platform-tests",
in `html/syntax/parsing/`. WPT keeps the `.dat` sources in
`html/syntax/parsing/resources/`, so they are taken from there, at the WPT
commit the other WPT suites in this repository are pinned to. The format
is described in `resources/README.md` at that commit (not vendored).

WPT keeps the files flat: the scripted cases are the files named
`scripted_*.dat` (html5lib-tests had them in a `scripted/` subdirectory).
Every `*.dat` file in `resources/` is copied byte for byte (62 files; each
matched the git blob hash GitHub reported for it). To update, copy the
same files from a newer WPT commit, change the commit above and the hashes
below, update `FILES` in the converter, and run `cargo xtask testdata`.

`xtask/src/testdata/html5lib_tree.rs` converts them into
`tests/generated/wpt_tree_construction.rs` (1,967 cases, plus a count
of the 6 scripted ones). It reads the fixed format (`#description`,
`#data`, `#errors`, `#new-errors`, `#document-fragment`, `#script-on`,
`#script-off`, `#document`) and fails on anything else. One deviation
upstream is accepted by name: `processing-instructions.dat` ends in an
extra empty line (the format says a single LF), which the converter drops;
if a later commit removes it, the conversion fails until the converter's
list is updated.

Not converted, and why:

- `#errors` and `#new-errors`: parse errors are not modelled.
- `#description`: read and dropped (16 cases have one; the file and index
  name the case).
- `scripted_*.dat`: these need a script engine; they are counted
  (`SCRIPTED_NOT_RUN`), never run.

## SHA-256

Of the 62 `.dat` files concatenated in byte order of their names
(`cat $(ls *.dat | LC_ALL=C sort) | shasum -a 256`):

    b387df2a6edb1e90bc89718382be0deea5bd0f44911560326cd6f2122441bce2

Of each file:

    b2aba05bd1d832f73a0c6103b3c8b151b283bab7c56887274d81f3a062c4963e  adoption01.dat
    e091e6976f861ae616fe56c527a78e7247ee7562bcafec996d4e4bda657bd9b7  adoption02.dat
    e3b7da1b57a4ec6991443dfc7ab3270f41d0f5959092a49be3e0edca0dae2104  blocks.dat
    c2f3a5ab4baf24f360ee14272aad18c33deffb9a56c2d5964777b1b6e0b8e3c1  comments01.dat
    f3a286c09d729eeed9aa63e0aec13ab12336af04590c169543e6d1e1ef4723b2  doctype01.dat
    eef4fb719e027ffaadfb854787d172893850fc561c29efe72d90c5bfa3c8b7ac  domjs-unsafe.dat
    b73605caac5aed5656184ab8db3f08edff5457ac3186cb04afa28384bca955e3  entities01.dat
    f4e0cd461204b0184709be040c00811b776fbde1a6d002bb1c75d02056d9e54a  entities02.dat
    73e1785753c66420c067e5b29f89b17e7ebe1079687a512040ef19c6d42ac2c2  foreign-fragment.dat
    bc8b465fe4a3ef199142d7f7e8bc6bf7ba10327d3dd795d7abef993bcfb352d0  html5test-com.dat
    cb722f2853ec9613b71ea68e8bb26f474cc450b64612930591ab2656406222fe  inbody01.dat
    d152de773e276a07a1cfc91e93f01f3ce52c447c110192f2828dab51be2721b6  isindex.dat
    d56e382994e1a5228ddb2ea49a5ff51ab68487f9a8f79ad34bcad05d40dc1e8f  main-element.dat
    3c2ecc07272c175676ecfafa0cf6e18e74c3293075703702a4b7929fcb0d07bd  math.dat
    08e5e25f38bbc181c840ce5c5203b2566dc03129aeaf105ca2311645d40aae4d  menuitem-element.dat
    318fbc9926eddf5863524f1503c711ddaea93b55bcbd1eaab71b7e354ddfeb09  namespace-sensitivity.dat
    e82449304a6371c14ed490384b6d814b7b1eeb1022dbc5caa2045fc8400655d7  noscript01.dat
    f45151f8dc7a4fe1a4b36710cf33606ff43cc98a42f1d2f085a77680683b0c99  pending-spec-changes-plain-text-unsafe.dat
    a6b7c4ecccabe70de2f24184245e4a73a8d12ed44ee658c3d5d25cce04c9d27f  pending-spec-changes.dat
    016ec8acc054e4e8d7f5c156687b0ed563f271b3ac928dad9a9f1566f6c5f8f5  plain-text-unsafe.dat
    3d4c6e67b59fda8fa0eb798106a42d244c69a84d7e3a385f9845bfc40071b4f1  processing-instructions.dat
    b6717cc15d4ed573ccf6755bc9d52073e675b4d09f23bde07961e27592b9717c  quirks01.dat
    5ae76ac4570d40e6648066798dd3ff729231bec98d3e010fdd67e0257f23a742  ruby.dat
    e32ea3adc3d68c90e62ea50b3a41bf80369d1491958532bf00787b3509667322  scriptdata01.dat
    1203be63238a6effc9cc47e3c9b1fa9a0c7e0126a2f78916514afed2d46f42d8  scripted_adoption01.dat
    93365261fd9ea7dd9242613b57c23dba94e66bfd837a5d928f725bed81012dd0  scripted_ark.dat
    4bc2c004bfd5efe3ca1b49f3b03de0b31d69347440c97ee1ed83b34ee16ad158  scripted_foster01.dat
    9d84f68ffd6e8b7b3924c9211280a70a888576b49074654cc9708236834afc58  scripted_webkit01.dat
    625ba3dcc1b8cf8688c0ee4ebd22308554a134b916f692bf64cbb54b8b705cae  search-element.dat
    4c819b8dbdfbd98cfbce9a535a304b0a16597eb29ccc04077131a62810f309cd  svg.dat
    bfd4a53246e3acc527c8bb214cc743082e19260e72365001aad3f1d8f4bd08dc  tables01.dat
    72667fae7be5d2020b679409e45fed7b6923a3e9394da11a02c5bd9650323264  template.dat
    aada6e3d12d624051bc978694475bd6a12bcedd7758781ba62425314684d23f3  tests1.dat
    2d2624a819c323661e396d864ac23440053127b5ea7adb44a5904f5ceee5fa64  tests10.dat
    276190e2a7b97e8fcf3bd863a4b4b5346b555a8336c00143cb1d0e8956b94a07  tests11.dat
    e6c506cea74979a0d6ca47f6b175c7b6177d6e57db708920a89694e31dfd8a42  tests12.dat
    d151b2426f38de40a5d4ae726e2a56dbc7742a9b1c95299d60c1e2e0fdad1f98  tests14.dat
    ef784ece74cbd760da3a6947aaf4478810246b73c753f25a04be4d11dd806b2d  tests15.dat
    3350be682713afc1f6dad37059f2551709497a3643c38c26e1fe36fd07d23745  tests16.dat
    0567680775f58a5b2ad24e234f41d53f68fb2fc3ef7809bebaec0920e2f13c89  tests17.dat
    5d0019ae43bb4e0b0da9f2e1d57ac0618a607bd8a1324b163ec7a23a1dc120f3  tests18.dat
    cb2f0875d14da9d96f939b7d549953f8f26e70ea14861935d07d828ab04e0e1d  tests19.dat
    9cf76b5f4890065c04fc82ae828379a55b85cbe76f584fb1ef23dcef0a77b86b  tests2.dat
    07f7661690c4cd7cc0bbb0f1b9c1e1d65135e07c4dde8bbf106692f687e7d33d  tests20.dat
    b1a67420c79a5131002fefc987084ffb6b6094a3a74b272c6f545a47df06452c  tests21.dat
    78488328181d0f82f34b1a5e9e456ff7c713b3ff86dab6ace1530f6f07d5370d  tests22.dat
    2e4752ff4ef898e4a0cf9a450e481440095163d45075a662846a062552afe148  tests23.dat
    fdd5c21f60f42235ded224a03e7182d289088328f460525adaf3c14e772a24ac  tests24.dat
    f2e08fda6d15a08faf9ff0001ec38560d942069cee6b4e264aeedbbacde7da8d  tests25.dat
    d55d24dfca2444fba759d59346cbab21f7e70340dbb14e2c7af8da3d44abd4ab  tests26.dat
    c4b4d8e0ea3d978c49d1e6a985d427164858b71ec980153c4526ed0c398f43b9  tests3.dat
    792f9bb43b2b233a43b126d456550d17beb533ce0af4a4d24e34f09a68fd44e5  tests4.dat
    bf80b927082290541781844906abdcb72f091488f7a11e8b7d9ac00076dd4fce  tests5.dat
    be16c74d2a9862283262968439c95b9bfce6182ea61055a3c886c28d14f3e01a  tests6.dat
    aeb9569589c809b1a563c0b163173e8cf980a6a4028cb7c210f19c181b56999a  tests7.dat
    f3c8b1baece162e7e8c394540cdf9057266bb738bb0ad539a9d9b2f9d365f162  tests8.dat
    857820f088506a6d20ea6acefbf19c0a6c4de87a39b24988878066397516b36f  tests9.dat
    acb9f835119e302d33204f437d54637a84ae26608ccb7bc961c6f7f44202a44c  tests_innerHTML_1.dat
    3fb6d24c5e371860d096ef07f5fff38be3ceaa85f1239bee35cce548b596198a  tricky01.dat
    c8855173aca8ecbd218abc26db34a631393ce0285fffebffdaf69b8bdd6224e9  void-in-phrasing.dat
    063ca232535a792fa238ae769eeb0ddcc9bd2ee961d3da327ca134612d35d93c  webkit01.dat
    03b215350d352faf110df2cc6eac23a44a7f70945b4ea962f0b17bed103459f7  webkit02.dat
