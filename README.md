<p align="center">
  Limbo is a work-in-progress, in-process OLTP database management system, compatible with SQLite.
</p>

---

## Features

* In-process OLTP database engine library
* Asynchronous I/O support on Linux with `io_uring`
* SQLite compatibility ([status](COMPAT.md))
  * SQL dialect support
  * File format support
  * SQLite C API
* JavaScript/WebAssembly bindings (_wip_)
* Support for Linux, macOS, and Windows

## Getting Started

### CLI

Install `limbo` with:

```shell 
curl --proto '=https' --tlsv1.2 -LsSf \
  https://github.com/penberg/limbo/releases/latest/download/limbo-installer.sh | sh
```

Then use the SQL shell to create and query a database:

```console
select * from sqlite_schema;
CREATE TABLE users (id INT PRIMARY KEY, username TEXT);
INSERT INTO users VALUES (1, 'alice');
SELECT * FROM users where id =1;
1|alice
```

## FAQ

### How is Limbo different from libSQL?

Limbo is a research project to build a SQLite compatible in-process database in Rust with native async support. The libSQL project, on the other hand, is an open source, open contribution fork of SQLite, with focus on production features such as replication, backups, encryption, and so on. There is no hard dependency between the two projects. Of course, if Limbo becomes widely successful, we might consider merging with libSQL, but that is something that will be decided in the future.

## Publications

* Pekka Enberg, Sasu Tarkoma, Jon Crowcroft Ashwin Rao (2024). Serverless Runtime / Database Co-Design With Asynchronous I/O. In _EdgeSys ‘24_. [[PDF]](https://penberg.org/papers/penberg-edgesys24.pdf)
* Pekka Enberg, Sasu Tarkoma, and Ashwin Rao (2023). Towards Database and Serverless Runtime Co-Design. In _CoNEXT-SW ’23_. [[PDF](https://penberg.org/papers/penberg-conext-sw-23.pdf)] [[Slides](https://penberg.org/papers/penberg-conext-sw-23-slides.pdf)]

## Contributing

We'd love to have you contribute to Limbo! Check out the [contribution guide] to get started.

## License

This project is licensed under the [MIT license].

### Contribution
[contribution guide]: https://github.com/penberg/limbo/blob/main/CONTRIBUTING.md

The following sequence diagram shows the typical flow of a query from the CLI to the [VDBE](https://www.sqlite.org/opcode.html).

```mermaid
sequenceDiagram

participant main as cli/main
participant Database as core/lib/Database
participant Connection as core/lib/Connection
participant Parser as sql/mod/Parser
participant translate as translate/mod
participant Statement as core/lib/Statement
participant Program as vdbe/mod/Program

main->>Database: open_file
Database->>main: Connection
main->>Connection: query(sql)
Note left of Parser: Parser uses vendored sqlite3-parser
Connection->>Parser: next()
Note left of Parser: Passes the SQL query to Parser

Parser->>Connection: Cmd::Stmt (ast/mod.rs)

Note right of translate: Translates SQL statement into bytecode
Connection->>translate:translate(stmt)

translate->>Connection: Program 

Connection->>main: Ok(Some(Rows { Statement }))

note right of main: a Statement with <br />a reference to Program is returned

main->>Statement: step()
Statement->>Program: step()
Note left of Program: Program executes bytecode instructions<br />See https://www.sqlite.org/opcode.html
Program->>Statement: StepResult
Statement->>main: StepResult
```

