package simple_trees

trait GenericConfig

// scala.annotation.internal.Child annotation with TERMREFin argument
sealed trait EmbeddedConfig extends GenericConfig:
  val config: String
end EmbeddedConfig

trait DefaultConfigs:
  val defaultConfig: EmbeddedConfig = PrivateConfig

  private case object PrivateConfig extends EmbeddedConfig:
    val config: String = "config"
  end PrivateConfig
end DefaultConfigs

object Configurations extends DefaultConfigs
